import HiddenCircuits.GraphReduction.UnitCoordinateExtractionCorrect
import HiddenCircuits.GraphReduction.Runtime.UnitOrderProgram
import HiddenCircuits.GraphReduction.UnitIntervalGraphInput

/-! Exact output semantics for the actual graph-to-coordinate pipeline. The
order and bounded relaxation coordinates are its own fixed algorithms. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionResult
open Complexity Complexity.BinaryArithmetic Polynomial UnitIntervalExtraction

def order (G : GraphInput) : List (Fin G.1):=UnitOrderSemantics.order (DH.Runtime.PairCheck.MatrixData.ofGraph G.2)
def coordinates (G : GraphInput) : Fin G.1→ℕ:=UnitCoordinateExtraction.coordinates G.2.graph (order G)
def denominator (G : GraphInput) : ℕ:=max 1 G.1
def bytes (G : GraphInput) : BitString:=encodeBitList
  (signedBits (denominator G:ℤ)::List.ofFn (fun i=>signedBits (coordinates G i:ℤ)))
def result (raw : BitString) : BitString:=
  match GraphInput.decode raw with
  | none=>[]
  | some G=>if UnitOrderProgram.accepts raw then bytes G else []

lemma coordinates_correct (G : GraphInput) (hu : RealUnitInterval.UnitIntervalGraph G.2.graph) :
    (∀i,coordinates G i+denominator G<2*G.1*denominator G) ∧
    ∀i j,G.2.graph.Adj i j ↔ i≠j ∧ coordinates G i ≤ coordinates G j+denominator G ∧
      coordinates G j ≤ coordinates G i+denominator G := by
  obtain ⟨hn,hc,horder⟩:=UnitOrderSemantics.order_ofGraph_correct G.2 hu
  exact UnitCoordinateExtraction.coordinates_correct G.2.graph (order G) hn hc horder

def representation (G : GraphInput) (hu : RealUnitInterval.UnitIntervalGraph G.2.graph) : GridRepresentation G.2.graph where
  left:=coordinates G
  adjacency i j:=by
    simpa only [UnitInterval.RationalGrid.denominator,Fintype.card_fin,denominator] using (coordinates_correct G hu).2 i j
  bound i:=by
    simpa only [UnitInterval.RationalGrid.denominator,Fintype.card_fin,denominator] using (coordinates_correct G hu).1 i
lemma bytes_representation (G : GraphInput) (hu : RealUnitInterval.UnitIntervalGraph G.2.graph) :
    bytes G=unitCoordinateBits G (UnitIntervalGraphInput.asIntegerInput G (representation G hu)) := by
  simp only [bytes,unitCoordinateBits,UnitIntervalGraphInput.asIntegerInput,representation,
    UnitInterval.RationalGrid.denominator,Fintype.card_fin,denominator]
lemma roundtrip (G : GraphInput) (hu : RealUnitInterval.UnitIntervalGraph G.2.graph) :
    CoordinateGraph.bits (bytes G)=G.encode := by
  rw [bytes_representation G hu]
  exact CoordinateGraph.bits_representation G _
lemma bytes_nonempty (G : GraphInput) : bytes G≠[] := by simp [bytes,encodeBitList]
lemma bytes_true_prefix (G : GraphInput) : ∃tail,bytes G=true::tail := by
  exact ⟨_,rfl⟩
lemma accepted {raw : BitString} {G : GraphInput} (hd : GraphInput.decode raw=some G)
    (hu : RealUnitInterval.UnitIntervalGraph G.2.graph) : result raw=bytes G := by
  have ha:UnitOrderProgram.accepts raw=true:=(UnitOrderProgram.accepts_iff raw).mpr ⟨G,hd,hu⟩
  simp [result,hd,ha]
lemma rejected (raw : BitString) (h : UnitOrderProgram.accepts raw=false) : result raw=[] := by
  cases hd:GraphInput.decode raw <;> simp [result,hd,h]
lemma nonempty_iff (raw : BitString) : result raw≠[] ↔ UnitOrderProgram.accepts raw=true := by
  cases hd:GraphInput.decode raw with
  | none=>simp [result,hd,UnitOrderProgram.accepts]
  | some G=>
    cases ha:UnitOrderProgram.accepts raw <;> simp [result,hd,ha,bytes_nonempty]

noncomputable def size : Polynomial ℕ:=8*(X+1)^3
lemma bytes_length (G : GraphInput) (hu : RealUnitInterval.UnitIntervalGraph G.2.graph) :
    (bytes G).length ≤ size.eval G.1 := by
  rw [bytes_representation G hu]
  have h:=UnitIntervalGraphInput.grid_bits_length G (representation G hu)
  simp only [size,eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
  have hp : G.1+1 ≤ (G.1+1)^3:=by nlinarith
  nlinarith
lemma result_length (raw : BitString) : (result raw).length ≤ size.eval raw.length := by
  by_cases ha:UnitOrderProgram.accepts raw=true
  · obtain ⟨G,hd,hu⟩:=(UnitOrderProgram.accepts_iff raw).mp ha
    rw [accepted hd hu]
    exact (bytes_length G hu).trans (polynomial_nat_eval_mono size (GraphInput.decode_vertices_bound hd))
  · have hf:UnitOrderProgram.accepts raw=false:=by cases h:UnitOrderProgram.accepts raw <;> simp_all
    rw [rejected raw hf]
    simp
end HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionResult
