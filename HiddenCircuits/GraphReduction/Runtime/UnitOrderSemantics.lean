import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionRounds

/-! Pure semantics of the two-array output extension. The saved component is
already reversed by the physical component scanner. Each round prepends that
array, so the final result reverses the concatenation of the successful
components, while preserving the original `Fin n` labels. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitOrderSemantics
open Complexity DH.Runtime.PairCheck

/-- The exact array copied from the first successful root's component state. -/
def savedOrder {n : ℕ} (G : MatrixData n) (A : Vector Bool n)
    (b : UnitRecognitionRoots.Best n) : List (Fin n) :=
  (b.map (fun r => (UnitRecognitionComponent.component G A r).order.reverse)).getD []

/-- Failed rounds stutter. Successful rounds retain their residual mask and
prepend their physically reversed label array to the accumulated array. -/
def run {n : ℕ} (G : MatrixData n) :
    ℕ → Vector Bool n → List (Fin n) → Vector Bool n × List (Fin n)
  | 0,A,acc => (A,acc)
  | fuel+1,A,acc =>
      let b := UnitRecognitionRoots.find G A
      run G fuel (UnitRecognitionRoots.residual G A b) (savedOrder G A b ++ acc)

/-- The graph-to-order function uses exactly the original vertex-count rounds. -/
def order {n : ℕ} (G : MatrixData n) : List (Fin n) :=
  (run G n (Vector.replicate n true) []).2

/-- The output is absent on rejection; no ordering or certificate is an input. -/
def recognize {n : ℕ} (G : MatrixData n) : Option (List (Fin n)) :=
  if UnitRecognitionRounds.accepts G then some (order G) else none

@[simp] theorem run_remaining {n : ℕ} (G : MatrixData n) (fuel : ℕ)
    (A : Vector Bool n) (acc : List (Fin n)) :
    (run G fuel A acc).1 = UnitRecognitionRounds.run G fuel A := by
  induction fuel generalizing A acc with
  | zero => rfl
  | succ fuel ih =>
    simpa only [run,UnitRecognitionRounds.run,UnitRecognitionRounds.round] using ih
      (UnitRecognitionRoots.residual G A (UnitRecognitionRoots.find G A))
      (savedOrder G A (UnitRecognitionRoots.find G A) ++ acc)

lemma run_stuck {n : ℕ} (G : MatrixData n) (fuel : ℕ)
    (A : Vector Bool n) (acc : List (Fin n))
    (h : UnitRecognitionRoots.find G A = none) : run G fuel A acc = (A,acc) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa only [run,h,savedOrder,Option.map_none,Option.getD_none,
      List.nil_append,UnitRecognitionRoots.residual] using ih

end HiddenCircuits.GraphReduction.Runtime.UnitOrderSemantics
