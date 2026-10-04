import HiddenCircuits.Complexity.UniqueTableau

/-! The actual finite TM2 verifier reaches a unique, canonically padded tableau.
This is the operational bridge for a later Boolean/CNF tableau encoding. -/
namespace HiddenCircuits.Complexity

private def optionStep {σ : Type*} (step : σ → Option σ) (c : Option σ) : Option σ := c.bind step

private lemma optionStep_none_iterate {σ : Type*} (step : σ → Option σ) (t : ℕ) :
    (optionStep step)^[t] none = none := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih]; rfl

/-- Reaching a configuration under mathlib's optional transition semantics agrees
with the stuttering semantics used for fixed-length tableaux. -/
private lemma stutter_iterate_of_some {σ : Type*} (step : σ → Option σ) (t : ℕ)
    {a b : σ} (h : (optionStep step)^[t] (some a) = some b) :
    (stutter step)^[t] a = b := by
  induction t generalizing a with
  | zero => exact Option.some.inj h
  | succ t ih =>
    rw [Function.iterate_succ_apply] at h ⊢
    cases hs : step a with
    | none =>
      simp only [optionStep,Option.bind_some,hs] at h
      rw [optionStep_none_iterate] at h
      contradiction
    | some c =>
      simp only [optionStep,Option.bind_some,hs] at h
      simp only [stutter,hs,Option.getD_some]
      exact ih h

/-- A verified bounded computation may be extended to its full time bound
without introducing any extra computation choices. -/
theorem evalsToInTime_stutter {σ : Type*} {step : σ → Option σ} {a b : σ} {t : ℕ}
    (h : StateTransition.EvalsToInTime step a (some b) t) (hb : step b = none) :
    (stutter step)^[t] a = b := by
  have he : (optionStep step)^[h.steps] (some a) = some b := h.evals_in_steps
  have hi := stutter_iterate_of_some step h.steps he
  calc
    (stutter step)^[t] a = (stutter step)^[t-h.steps] ((stutter step)^[h.steps] a) := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel h.steps_le_m]
    _ = b := by rw [hi,stutter_iterate_halt hb]

theorem tm2_stutter_output (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀))
    (output : List (tm.Γ tm.k₁)) (t : ℕ)
    (h : Turing.TM2OutputsInTime tm input (some output) t) :
    (stutter tm.step)^[t] (Turing.initList tm input) = Turing.haltList tm output := by
  apply evalsToInTime_stutter h
  rfl

lemma haltList_injective (tm : Turing.FinTM2) : Function.Injective (Turing.haltList tm) := by
  intro x y h
  have he := congrArg (fun c : tm.Cfg => c.stk tm.k₁) h
  simpa [Turing.haltList] using he

namespace VerifierTableau
variable {v : BitString → Bool}
variable (M : Turing.TM2ComputableInPolyTime id Computability.encodeBool v)

def initial (x : BitString) {m : ℕ} (w : Fin m → Bool) : M.tm.Cfg :=
  Turing.initList M.tm ((pairBits x (List.ofFn w)).map M.inputAlphabet.invFun)

def output (b : Bool) : M.tm.Cfg :=
  Turing.haltList M.tm ((Computability.encodeBool b).map M.outputAlphabet.invFun)

def horizon (x : BitString) (m : ℕ) : ℕ := M.time.eval (2*x.length+m+1)

theorem output_injective : Function.Injective (output M) := by
  intro a b h
  apply M.outputAlphabet.symm.injective
  have hh := haltList_injective M.tm h
  simpa [Computability.encodeBool] using hh

/-- The fixed tableau horizon is a polynomial in input plus certificate length. -/
theorem final_output (x : BitString) {m : ℕ} (w : Fin m → Bool) :
    (stutter M.tm.step)^[horizon M x m] (initial M x w) =
      output M (v (pairBits x (List.ofFn w))) := by
  have h := M.outputsFun (pairBits x (List.ofFn w))
  simp only [id_eq,pairBits_length,List.length_ofFn] at h
  exact tm2_stutter_output M.tm _ _ _ h

/-- Acceptance of the padded actual machine tableau is exactly acceptance of its
certificate, with no accepting-state or halt-padding multiplicity. -/
theorem accepts_iff (x : BitString) {m : ℕ} (w : Fin m → Bool) :
    (stutter M.tm.step)^[horizon M x m] (initial M x w) = output M true ↔
      v (pairBits x (List.ofFn w)) = true := by
  rw [final_output M x w]
  exact (output_injective M).eq_iff

noncomputable def certificateEquiv (x : BitString) (m : ℕ) :
    {w : Fin m → Bool // v (pairBits x (List.ofFn w)) = true} ≃
    AcceptedTableau (stutter M.tm.step) (initial M x (m := m)) (horizon M x m) (fun c => c = output M true) :=
  (Equiv.subtypeEquivRight (fun w => (accepts_iff M x w).symm)).trans
    (acceptedTableauEquiv (stutter M.tm.step) (initial M x (m := m))
      (horizon M x m) (fun c => c = output M true))

/-- #P's count equals the number of accepted tableaux of its actual finite TM2
verifier. Encoding these configurations and constraints as Boolean CNF is separate. -/
theorem certificateCount_eq_tableaux (x : BitString) (m : ℕ) :
    certificateCount v x m = Fintype.card
      (AcceptedTableau (stutter M.tm.step) (initial M x (m := m)) (horizon M x m) (fun c => c = output M true)) := by
  classical
  exact Fintype.card_congr (certificateEquiv M x m)

end VerifierTableau
end HiddenCircuits.Complexity
