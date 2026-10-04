import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionGate
import HiddenCircuits.GraphReduction.UnitIntervalRestrictedCount

/-! Connecting the physical gate to the literal total unit-interval restricted
count.  The hypotheses explicitly require a finite query-free recognizer and its
charged execution theorem; semantic recognition alone is not a time certificate. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRecognitionGate
open Complexity UnitIntervalRecognition
variable {k : ℕ}

/-- The Boolean semantic contract for the total ordinary-graph recognizer. -/
def acceptsUnitGraph (xs : BitString) : Bool :=
  match GraphInput.decode xs with
  | none => false
  | some G => (recognize G.2.graph).isSome

lemma restrictedProblem_eq_gated (xs : BitString) :
    restrictedProblem xs =
      if acceptsUnitGraph xs then GraphInput.perfectMatchingProblem xs else 0 := by
  cases hd : GraphInput.decode xs <;>
    simp [restrictedProblem,acceptsUnitGraph,GraphInput.perfectMatchingProblem,hd]

/-- The gate agrees with the specified total count on every byte string,
including malformed inputs and valid graphs outside the class. -/
lemma restrictedProblem_eq_graphGate (xs : BitString) :
    restrictedProblem xs = GraphInput.perfectMatchingProblem (graphGate acceptsUnitGraph xs) := by
  rw [graphGate_count]
  exact restrictedProblem_eq_gated xs

/-- A recognizer may use any extension on malformed inputs: the downstream
ordinary graph verifier already assigns those strings count zero. -/
lemma restrictedProblem_eq_gated_of_valid (accept : BitString → Bool)
    (hspec : ∀ xs G, GraphInput.decode xs=some G →
      accept xs=(recognize G.2.graph).isSome) (xs : BitString) :
    restrictedProblem xs =
      if accept xs then GraphInput.perfectMatchingProblem xs else 0 := by
  cases hd : GraphInput.decode xs with
  | none => simp [restrictedProblem,GraphInput.perfectMatchingProblem,hd]
  | some G => simp [restrictedProblem,GraphInput.perfectMatchingProblem,hd,hspec xs G hd]

/-- Plug an actual compiled recognizer into the physical gate to obtain #P
membership for the literal zero-on-reject restricted matching count. -/
theorem restrictedProblem_sharpP_of_recognizer (B : OracleBlock k) (hB : B.QueryFree)
    (accept : BitString → Bool) (p : Polynomial ℕ)
    (hrun : ∀ xs, ∃ s c,
      B.Executes (fun _=>0) (Function.update (fun _=>[]) 0 xs) s c ∧
      s 0=Computability.encodeBool (accept xs) ∧ c≤p.eval xs.length)
    (hspec : ∀ xs G, GraphInput.decode xs=some G →
      accept xs=(recognize G.2.graph).isSome) : SharpP restrictedProblem := by
  have he : restrictedProblem =
      (fun xs => if accept xs then GraphInput.perfectMatchingProblem xs else 0) :=
    funext (restrictedProblem_eq_gated_of_valid accept hspec)
  rw [he]
  exact sharpP_of_recognizer B hB accept p hrun

/-- Specialization when the compiled recognizer implements the exact total
Boolean function above. -/
theorem restrictedProblem_sharpP_of_exact_recognizer (B : OracleBlock k)
    (hB : B.QueryFree) (p : Polynomial ℕ)
    (hrun : ∀ xs, ∃ s c,
      B.Executes (fun _=>0) (Function.update (fun _=>[]) 0 xs) s c ∧
      s 0=Computability.encodeBool (acceptsUnitGraph xs) ∧ c≤p.eval xs.length) :
    SharpP restrictedProblem := by
  apply restrictedProblem_sharpP_of_recognizer B hB acceptsUnitGraph p hrun
  intro xs G hd
  simp [acceptsUnitGraph,hd]

end HiddenCircuits.GraphReduction.Runtime.UnitRecognitionGate
