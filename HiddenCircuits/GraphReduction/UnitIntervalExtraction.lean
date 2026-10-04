import HiddenCircuits.GraphReduction.UnitIntervalRecognition
import HiddenCircuits.GraphReduction.UnitIntervalOrderConstruction
import HiddenCircuits.GraphReduction.RationalUnitIntervalGrid

/-! Executable ordinary-graph recognition and bounded integer-grid extraction.
The graph supplies adjacency only. Every order and coordinate is constructed.
This is the high-level executable frontend; no bit-machine time bound is claimed
by these declarations alone. -/
namespace HiddenCircuits.GraphReduction.UnitIntervalExtraction
open UnitIntervalOrder UnitIntervalRecognition
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The supplied order proof is used internally after the recognizer constructs
and checks its vertex list; all executable arithmetic is in `buildModel`. -/
def representationOfOrderedList (ls : List V) (hn : ls.Nodup) (hc : ∀ v, v ∈ ls)
    (hu : ListUmbrella G ls) : UnitInterval.Representation G := by
  let e := hn.getEquivOfForallMemList ls hc
  let r := (buildModel ls.length (G.comap ls.get) hu).representation
  refine { length := r.length, positive := r.positive, left := fun v => r.left (e.symm v), adjacency := ?_ }
  intro v w
  have he : ∀ i, e i = ls.get i := fun _ => rfl
  have hv : ls.get (e.symm v) = v := by rw [←he]; exact e.apply_symm_apply v
  have hw : ls.get (e.symm w) = w := by rw [←he]; exact e.apply_symm_apply w
  simpa only [SimpleGraph.comap_adj,hv,hw,ne_eq,e.symm.injective.eq_iff]
    using r.adjacency (e.symm v) (e.symm w)

/-- Denominator n (or one for the empty input), with nonnegative quadratic
numerators and exact closed-interval adjacency. -/
structure GridRepresentation (G : SimpleGraph V) where
  left : V → ℕ
  adjacency : ∀ v w, G.Adj v w ↔ v ≠ w ∧
    left v ≤ left w + UnitInterval.RationalGrid.denominator (V:=V) ∧
    left w ≤ left v + UnitInterval.RationalGrid.denominator (V:=V)
  bound : ∀ v, left v + UnitInterval.RationalGrid.denominator (V:=V) <
    2 * Fintype.card V * UnitInterval.RationalGrid.denominator (V:=V)

def ofRational (r : UnitInterval.Representation G) : GridRepresentation G where
  left := UnitInterval.RationalGrid.numerator r.unitLength.left
  bound := UnitInterval.RationalGrid.endpoint_bound r.unitLength.left
  adjacency v w := by
    rw [r.unitLength.adjacency,UnitInterval.icc_overlap
      (by change r.unitLength.left v ≤ r.unitLength.left v+1; linarith)
      (by change r.unitLength.left w ≤ r.unitLength.left w+1; linarith)]
    change (v ≠ w ∧ r.unitLength.left v ≤ r.unitLength.left w+1 ∧
      r.unitLength.left w ≤ r.unitLength.left v+1) ↔ _
    rw [←UnitInterval.RationalGrid.comparison r.unitLength.left v w,
      ←UnitInterval.RationalGrid.comparison r.unitLength.left w v]

/-- Total graph-to-grid algorithm, rejecting exactly the non-unit-interval
inputs. Neither an ordering nor a representation is an argument. -/
def extract (G : SimpleGraph V) [DecidableRel G.Adj] : Option (GridRepresentation G) :=
  match he : recognize G with
  | none => none
  | some ls =>
    let hs := search_sound (Fintype.card V) G ls he
    some (ofRational (representationOfOrderedList ls hs.1 hs.2.1 hs.2.2))

lemma extract_isSome (G : SimpleGraph V) [DecidableRel G.Adj] :
    (extract G).isSome = (recognize G).isSome := by
  unfold extract
  split <;> simp_all

/-- The literal executable output accepts precisely the semantic real class. -/
theorem extract_iff (G : SimpleGraph V) [DecidableRel G.Adj] :
    (extract G).isSome = true ↔ RealUnitInterval.UnitIntervalGraph G := by
  rw [extract_isSome,recognize_iff]

end HiddenCircuits.GraphReduction.UnitIntervalExtraction
