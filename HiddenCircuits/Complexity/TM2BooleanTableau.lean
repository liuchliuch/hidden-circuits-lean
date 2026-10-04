import HiddenCircuits.Complexity.TM2BooleanStep

/-! Uniform-height Boolean simulation of an entire actual polynomial-time
verifier execution, including exact certificate acceptance. -/
namespace HiddenCircuits.Complexity.TM2BooleanEncoding
attribute [local instance] Classical.propDecidable

theorem input_valid_at_horizon (M : Turing.FinTM2) (x : List (M.Γ M.k₀)) (t T : ℕ) (ht : t ≤ T) :
    Valid M (x.length+T*TM2Space.machineBudget M)
      ((stutter M.step)^[t] (Turing.initList M x)) := by
  have h := input_tableau_valid M x t
  refine ⟨h.1,fun k => (h.2 k).trans ?_⟩
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ ht) _

/-- Every row has the same polynomial-size encoding, so padding is canonical. -/
theorem stepCode_iterate_input (M : Turing.FinTM2) (x : List (M.Γ M.k₀)) (T t : ℕ) (ht : t ≤ T) :
    (stepCode M (x.length+T*TM2Space.machineBudget M))^[t]
      (encode M (x.length+T*TM2Space.machineBudget M) (Turing.initList M x)) =
    encode M (x.length+T*TM2Space.machineBudget M)
      ((stutter M.step)^[t] (Turing.initList M x)) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',ih (by omega)]
    exact stepCode_encode _ _ _ (input_valid_at_horizon M x t T (by omega))

end HiddenCircuits.Complexity.TM2BooleanEncoding

namespace HiddenCircuits.Complexity.VerifierTableau
variable {v : BitString → Bool}
variable (M : Turing.TM2ComputableInPolyTime id Computability.encodeBool v)
attribute [local instance] Classical.propDecidable

/-- One polynomial gives a common tableau horizon for every certificate. -/
noncomputable def horizonPolynomial (p : Polynomial ℕ) : Polynomial ℕ :=
  M.time.comp (2*Polynomial.X+p+1)

theorem horizonPolynomial_eval (p : Polynomial ℕ) (x : BitString) :
    (horizonPolynomial M p).eval x.length = horizon M x (p.eval x.length) := by
  simp [horizonPolynomial,horizon,Polynomial.eval_comp]

def height (x : BitString) (m : ℕ) : ℕ :=
  2*x.length+m+1+(horizon M x m)*TM2Space.machineBudget M.tm

noncomputable def initialCode (x : BitString) {m : ℕ} (w : Fin m → Bool) :
    TM2BooleanEncoding.Cell M.tm (height M x m) → Bool :=
  TM2BooleanEncoding.encode M.tm (height M x m) (initial M x w)

noncomputable def finalCode (x : BitString) {m : ℕ} (w : Fin m → Bool) :
    TM2BooleanEncoding.Cell M.tm (height M x m) → Bool :=
  (TM2BooleanEncoding.stepCode M.tm (height M x m))^[horizon M x m] (initialCode M x w)

theorem finalCode_eq (x : BitString) {m : ℕ} (w : Fin m → Bool) :
    finalCode M x w = TM2BooleanEncoding.encode M.tm (height M x m)
      (output M (v (pairBits x (List.ofFn w)))) := by
  have h := TM2BooleanEncoding.stepCode_iterate_input M.tm
    ((pairBits x (List.ofFn w)).map M.inputAlphabet.invFun) (horizon M x m) (horizon M x m) le_rfl
  rw [show ((pairBits x (List.ofFn w)).map M.inputAlphabet.invFun).length = 2*x.length+m+1 by simp] at h
  change finalCode M x w = TM2BooleanEncoding.encode M.tm (height M x m)
    ((stutter M.tm.step)^[horizon M x m] (initial M x w)) at h
  exact h.trans (congrArg (TM2BooleanEncoding.encode M.tm (height M x m)) (final_output M x w))

theorem finalOutput_valid (x : BitString) {m : ℕ} (w : Fin m → Bool) :
    TM2BooleanEncoding.Valid M.tm (height M x m) (output M (v (pairBits x (List.ofFn w)))) := by
  have h := TM2BooleanEncoding.input_tableau_valid M.tm
    ((pairBits x (List.ofFn w)).map M.inputAlphabet.invFun) (horizon M x m)
  simp only [List.length_map,pairBits_length,List.length_ofFn] at h
  change TM2BooleanEncoding.Valid M.tm (height M x m)
    ((stutter M.tm.step)^[horizon M x m] (initial M x w)) at h
  rwa [final_output M x w] at h

/-- Read the true output symbol through the explicit finite one-hot decoder. -/
noncomputable def acceptCode (H : ℕ) (bits : TM2BooleanEncoding.Cell M.tm H → Bool) : Bool := by
  classical
  exact decide ((TM2BooleanEncoding.decodeSlot M.tm H bits M.tm.k₁ 0).map Subtype.val =
    some (M.outputAlphabet.invFun true))

/-- The concrete Boolean simulation accepts exactly the original certificates. -/
theorem finalCode_accepts_iff (x : BitString) {m : ℕ} (w : Fin m → Bool) :
    acceptCode M (height M x m) (finalCode M x w) = true ↔
      v (pairBits x (List.ofFn w)) = true := by
  classical
  rw [finalCode_eq]
  unfold acceptCode
  rw [decide_eq_true_eq,TM2BooleanEncoding.decodeSlot_encode M.tm _ _ (finalOutput_valid M x w)]
  simp [output,Turing.haltList,Computability.encodeBool]

/-- A concrete Boolean evolution preserves #P's certificate multiplicities. -/
theorem certificateCount_eq_boolean (x : BitString) (m : ℕ) :
    certificateCount v x m = Nat.card {w : Fin m → Bool //
      acceptCode M (height M x m) (finalCode M x w) = true} := by
  classical
  unfold certificateCount
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun w => (finalCode_accepts_iff M x w).symm))

end HiddenCircuits.Complexity.VerifierTableau
