import HiddenCircuits.Complexity.UniformTableau
import HiddenCircuits.Complexity.TM2FiniteRuleTable

/-! The exact count-preserving verifier formula used by the operational emitter:
row-major iteration and direct fixed-boundary local rule tables. -/
namespace HiddenCircuits.Complexity.VerifierTableau
open TM2BooleanEncoding
variable {v : BitString → Bool}
variable (M : Turing.TM2ComputableInPolyTime id Computability.encodeBool v)

noncomputable def uniformPositiveFormula (x : BitString) (m : ℕ) (ht : HasTrueSymbol M) :=
  InitialNetwork.orderedCNF (directNetwork M.tm (height M x m)) (horizon M x m)
    (sources M x m) (outputWire M x m ht)

theorem uniformPositiveFormula_count (x : BitString) (m : ℕ) (ht : HasTrueSymbol M) :
    (uniformPositiveFormula M x m ht).satCount = certificateCount v x m := by
  classical
  unfold uniformPositiveFormula
  rw [InitialNetwork.orderedCNF_count,InitialNetwork.toCNF_count,directNetwork_step_eq]
  unfold certificateCount
  conv_rhs => rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun w => by rw [finalNetwork_value M x m ht w]))

noncomputable def uniformFormula (x : BitString) (m : ℕ) : CNFInput := by
  classical
  exact if ht : HasTrueSymbol M then ⟨_,_,uniformPositiveFormula M x m ht⟩ else ⟨m,1,rejectingCNF m⟩

lemma uniformFormula_pos (x : BitString) (m : ℕ) (ht : HasTrueSymbol M) :
    uniformFormula M x m = ⟨_,_,uniformPositiveFormula M x m ht⟩ := by
  unfold uniformFormula;exact dif_pos ht

lemma uniformFormula_neg (x : BitString) (m : ℕ) (ht : ¬ HasTrueSymbol M) :
    uniformFormula M x m = ⟨m,1,rejectingCNF m⟩ := by
  unfold uniformFormula;exact dif_neg ht

theorem uniformFormula_count (x : BitString) (m : ℕ) :
    (uniformFormula M x m).2.2.satCount = certificateCount v x m := by
  classical
  by_cases ht : HasTrueSymbol M
  · rw [uniformFormula_pos M x m ht]
    exact uniformPositiveFormula_count M x m ht
  · rw [uniformFormula_neg M x m ht]
    exact (rejectingCNF_count m).trans (no_true_symbol_count M x m ht).symm

theorem uniformFormula_polynomial_size (p : Polynomial ℕ) (x : BitString) :
    (CNFInput.encode (uniformFormula M x (p.eval x.length))).length ≤ (formulaSizePolynomial M p).eval x.length := by
  classical
  rw [formulaSizePolynomial_eval]
  by_cases ht : HasTrueSymbol M
  · rw [uniformFormula_pos M x _ ht]
    exact (InitialNetwork.orderedCNF_bits _ _ _ _).trans (by omega)
  · rw [uniformFormula_neg M x _ ht]
    change (rejectingCNF (p.eval x.length)).bits.length ≤ _
    rw [rejectingCNF_bits];omega

end HiddenCircuits.Complexity.VerifierTableau
