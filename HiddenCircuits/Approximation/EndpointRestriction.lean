import HiddenCircuits.Approximation.CanonicalPaths.MonotoneRectangle
import HiddenCircuits.GraphReduction.PermutationMonotone

/-! Boundary counts and retained
vertex order preserve the original runtime-facing restriction interface. -/
namespace HiddenCircuits.Approximation.MonotoneEndpoints
open GraphReduction
variable {n m : ℕ} (E : MonotoneEndpoints n)

def restrict (rows columns : Fin m ↪ Fin n) (hr : StrictMono rows) (hc : StrictMono columns) :
    MonotoneEndpoints m where
  lo i := endpointCount (fun j => (columns j).val) (E.lo (rows i))
  hi i := endpointCount (fun j => (columns j).val) (E.hi (rows i))
  lo_mono := (endpointCount_mono _).comp (E.lo_mono.comp hr.monotone)
  hi_mono := (endpointCount_mono _).comp (E.hi_mono.comp hr.monotone)
  lo_le_hi i := endpointCount_mono _ (E.lo_le_hi (rows i))
  hi_le i := by
    simpa only [Fintype.card_fin] using endpointCount_upper (fun j => (columns j).val) (E.hi (rows i))

theorem restrict_allowed (rows columns : Fin m ↪ Fin n) (hr : StrictMono rows) (hc : StrictMono columns)
    (i j : Fin m) :
    ((E.restrict rows columns hr hc).lo i ≤ j.val ∧ j.val < (E.restrict rows columns hr hc).hi i) ↔
      (E.lo (rows i) ≤ (columns j).val ∧ (columns j).val < E.hi (rows i)) := by
  have hmono : StrictMono (fun j => (columns j).val) := fun a b h => hc h
  have hlo := endpointCount_index (fun j => (columns j).val) hmono j (E.lo (rows i))
  have hhi := endpointCount_index (fun j => (columns j).val) hmono j (E.hi (rows i))
  change (endpointCount (fun j => (columns j).val) (E.lo (rows i)) ≤ j.val ∧
    j.val < endpointCount (fun j => (columns j).val) (E.hi (rows i))) ↔ _
  omega

end HiddenCircuits.Approximation.MonotoneEndpoints
