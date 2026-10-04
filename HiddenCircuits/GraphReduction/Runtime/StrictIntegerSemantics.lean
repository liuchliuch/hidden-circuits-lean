import HiddenCircuits.GraphReduction.Runtime.StrictIntegerHeader
import HiddenCircuits.Complexity.GraphVerifier.MatchingPullback

/-! The literal integer-radius input of the paper: adjacency is STRICT distance
less than r. Labels remain distinct even at coincident coordinates.

The total extension uses the bounded permissive word-list decoder. A missing
radius decodes to zero; malformed sign/magnitude words are normalized and the
list marker is consumed even when malformed. Nonpositive radii produce no
edges. A decoded empty list has one empty matching, including on malformed
inputs; these conventions are explicit and are outside the positive-radius
promise of the paper. -/
namespace HiddenCircuits.GraphReduction
open Complexity Complexity.BinaryArithmetic

structure StrictIntegerRepresentation (G : GraphInput) where
  radius : ℤ
  positive : 0<radius
  coordinate : Fin G.1 → ℤ
  adjacency : ∀i j,G.2.graph.Adj i j ↔i≠j ∧ |coordinate i-coordinate j|<radius

def strictIntegerBits (G : GraphInput) (R : StrictIntegerRepresentation G) : BitString :=
  encodeBitList (signedBits R.radius::List.ofFn (fun i=>signedBits (R.coordinate i)))

def StrictIntegerOracle (g : BitString → ℕ) : Prop :=
  ∀ (G : GraphInput) (R : StrictIntegerRepresentation G),
    g (strictIntegerBits G R)=perfectMatchingCount G.2.graph

/-- Labelled integer coordinates, with literal strict-radius adjacency. -/
def strictIntegerGraph {n : ℕ} (r : ℤ) (x : Fin n → ℤ) : MatrixGraph n where
  edge i j := decide (i≠j ∧ |x i-x j|<r)
  symm i j := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,ne_comm,abs_sub_comm]
  loopless i := by simp

def strictIntegerRepresentation {n : ℕ} (r : ℤ) (hr:0<r) (x : Fin n → ℤ) :
    StrictIntegerRepresentation ⟨n,strictIntegerGraph r x⟩ where
  radius := r
  positive := hr
  coordinate := x
  adjacency i j := by simp [strictIntegerGraph,MatrixGraph.graph]

namespace Runtime.StrictInteger
open OracleBlock Polynomial

def radius (xs : BitString) : ℤ := CoordinateGraph.denominator xs
def data (xs : BitString) : BitString := CoordinateGraph.coordinates xs
def edge (xs : BitString) (i j : ℕ) : Bool :=
  decide (i≠j ∧ |CoordinateGraph.endpoint (data xs) i-CoordinateGraph.endpoint (data xs) j|<radius xs)
def graph (xs : BitString) : MatrixGraph (LooseWordList.words (data xs)).length where
  edge i j := edge xs i.val j.val
  symm i j := by
    apply Bool.eq_iff_iff.mpr
    simp only [edge,decide_eq_true_eq,ne_comm,abs_sub_comm]
  loopless i := by simp [edge]
def graphInput (xs : BitString) : GraphInput := ⟨_,graph xs⟩
def bits (xs : BitString) : BitString := CoordinateGraph.bits (StrictIntegerHeader.bits true xs)

lemma threshold (r x y : ℤ) : (x-y≤r-1 ∧y-x≤r-1) ↔|x-y|<r := by
  rw [abs_lt]
  omega

lemma edge_eq (xs : BitString) (i j : ℕ) :
    CoordinateGraph.edge (radius xs-1) (data xs) i j=edge xs i j := by
  apply Bool.eq_iff_iff.mpr
  simp only [CoordinateGraph.edge,IntegerDistance.answer,edge,Bool.and_eq_true,decide_eq_true_eq,threshold]

lemma bits_graph (xs : BitString) : bits xs=(graphInput xs).encode := by
  have hh : CoordinateGraph.denominator (StrictIntegerHeader.bits true xs)=radius xs-1 := by
    simp [CoordinateGraph.denominator,StrictIntegerHeader.bits,LooseWordList.head,
      StrictIntegerHeader.delta,radius]
    omega
  have ht : CoordinateGraph.coordinates (StrictIntegerHeader.bits true xs)=data xs := by
    simp [CoordinateGraph.coordinates,StrictIntegerHeader.bits,LooseWordList.tail,data]
  unfold bits CoordinateGraph.bits
  rw [hh,ht]
  apply MatrixEmitter.queryBits_graph
  intro i j
  exact edge_eq xs i.val j.val

lemma bits_representation (G : GraphInput) (R : StrictIntegerRepresentation G) :
    bits (strictIntegerBits G R)=G.encode := by
  rcases G with ⟨n,G⟩
  have he : ∀i j : Fin n,CoordinateGraph.edge (R.radius-1)
      (encodeBitList (List.ofFn (fun i=>signedBits (R.coordinate i)))) i.val j.val=G.edge i j := by
    intro i j
    apply Bool.eq_iff_iff.mpr
    simp only [CoordinateGraph.edge,IntegerDistance.answer,Bool.and_eq_true,decide_eq_true_eq,
      CoordinateGraph.endpoint,LooseWordList.words_encode]
    simp only [List.getElem?_ofFn,i.isLt,j.isLt,dite_true,Option.getD_some,SignedNormalize.value_signedBits]
    change (i.val≠j.val ∧R.coordinate i-R.coordinate j≤R.radius-1 ∧
      R.coordinate j-R.coordinate i≤R.radius-1) ↔G.graph.Adj i j
    rw [R.adjacency,threshold]
    simp [Fin.ext_iff]
  change CoordinateGraph.bits (StrictIntegerHeader.bits true
    (encodeBitList (signedBits R.radius::List.ofFn (fun i=>signedBits (R.coordinate i)))))=GraphInput.encode ⟨n,G⟩
  rw [StrictIntegerHeader.bits_encode]
  simp only [StrictIntegerHeader.delta,if_true,←sub_eq_add_neg]
  simpa only [CoordinateGraph.bits,CoordinateGraph.coordinates,
    CoordinateGraph.denominator,LooseWordList.tail,LooseWordList.head,encodeBitList,
    GraphVerifier.parse_pair,LooseWordList.words_encode,List.length_ofFn,SignedNormalize.value_signedBits] using
    MatrixEmitter.queryBits_graph G (CoordinateGraph.edge (R.radius-1)
      (encodeBitList (List.ofFn (fun i=>signedBits (R.coordinate i))))) he

lemma nonpositive_no_edges (xs : BitString) (hr:radius xs≤0) (i j : ℕ) : edge xs i j=false := by
  simp only [edge,decide_eq_false_iff_not]
  intro h
  have := abs_nonneg (CoordinateGraph.endpoint (data xs) i-CoordinateGraph.endpoint (data xs) j)
  omega

end Runtime.StrictInteger
end HiddenCircuits.GraphReduction
