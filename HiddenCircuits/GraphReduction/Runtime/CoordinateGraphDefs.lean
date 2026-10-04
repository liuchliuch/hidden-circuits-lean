import HiddenCircuits.GraphReduction.Runtime.UnitCoordinateHardness
import HiddenCircuits.GraphReduction.Runtime.IntegerDistanceDefs
import HiddenCircuits.Complexity.BinaryArithmetic.SignedNormalize
import HiddenCircuits.Complexity.LooseWordList
import HiddenCircuits.Complexity.MatrixEmitterGraph

/-! The graph interpreted from integer-coordinate input bytes, with an arbitrary
but total permissive extension away from canonical representations. -/
namespace HiddenCircuits.GraphReduction.Runtime.CoordinateGraph
open Complexity Complexity.BinaryArithmetic

def denominator (xs : BitString) : ℤ := SignedNormalize.value (LooseWordList.head xs)
def coordinates (xs : BitString) : BitString := LooseWordList.tail xs
def endpoint (data : BitString) (i : ℕ) : ℤ := SignedNormalize.value ((LooseWordList.words data)[i]?.getD [])
def edge (d : ℤ) (data : BitString) (i j : ℕ) : Bool :=
  decide (i≠j) &&IntegerDistance.answer d (endpoint data i) (endpoint data j)
def bits (xs : BitString) : BitString :=
  MatrixEmitter.queryBits (LooseWordList.words (coordinates xs)).length (edge (denominator xs) (coordinates xs))

lemma integer_intervals (d x y : ℤ) (hd:0<d) :
    ((Set.Icc ((x:ℚ)/d) ((x:ℚ)/d+1)∩Set.Icc ((y:ℚ)/d) ((y:ℚ)/d+1)).Nonempty) ↔
      (x-y≤d ∧y-x≤d) := by
  have hdq:(0:ℚ)<d := by exact_mod_cast hd
  have hxy (a b : ℤ) : (a:ℚ)/d≤(b:ℚ)/d+1 ↔a-b≤d := by
    have he : (b:ℚ)/d+1=((b:ℚ)+d)/d := by field_simp [ne_of_gt hdq]
    rw [he,div_le_div_iff_of_pos_right hdq]
    have h : a≤b+d ↔a-b≤d := by omega
    exact_mod_cast h
  rw [Set.Icc_inter_Icc,Set.nonempty_Icc]
  simp only [max_le_iff,le_min_iff,hxy]
  constructor
  · tauto
  · rintro ⟨h1,h2⟩
    exact ⟨⟨by linarith,h2⟩,⟨h1,by linarith⟩⟩

theorem bits_representation (G : GraphInput) (R : UnitIntegerRepresentation G) :
    bits (unitCoordinateBits G R)=G.encode := by
  rcases G with ⟨n,G⟩
  have he : ∀i j : Fin n,edge R.denominator (encodeBitList (List.ofFn (fun i=>signedBits (R.left i)))) i.val j.val=G.edge i j := by
    intro i j
    apply Bool.eq_iff_iff.mpr
    simp only [edge,IntegerDistance.answer,Bool.and_eq_true,decide_eq_true_eq,endpoint,LooseWordList.words_encode]
    simp only [List.getElem?_ofFn,i.isLt,j.isLt,dite_true,Option.getD_some,SignedNormalize.value_signedBits]
    change (i.val≠j.val ∧R.left i-R.left j≤R.denominator ∧R.left j-R.left i≤R.denominator) ↔G.graph.Adj i j
    rw [R.adjacency,integer_intervals _ _ _ R.positive]
    simp [Fin.ext_iff]
  simpa only [bits,unitCoordinateBits,coordinates,denominator,LooseWordList.tail,LooseWordList.head,
    encodeBitList,GraphVerifier.parse_pair,LooseWordList.words_encode,List.length_ofFn,SignedNormalize.value_signedBits] using
    MatrixEmitter.queryBits_graph G (edge R.denominator (encodeBitList (List.ofFn (fun i=>signedBits (R.left i))))) he

lemma coordinate_length (xs : BitString) : (coordinates xs).length≤xs.length := LooseWordList.tail_length xs
lemma vertices_length (xs : BitString) : (LooseWordList.words (coordinates xs)).length≤xs.length :=
  (LooseWordList.words_length _).trans (coordinate_length xs)
lemma bits_length (xs : BitString) : (bits xs).length≤xs.length^2+2*xs.length+1 := by
  have hn:=vertices_length xs
  simp only [bits,MatrixEmitter.queryBits,pairBits_length,List.length_replicate,MatrixEmitter.matrixBits_length]
  nlinarith
end HiddenCircuits.GraphReduction.Runtime.CoordinateGraph
