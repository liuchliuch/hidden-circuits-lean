import HiddenCircuits.Complexity.TM2InitialSources
import HiddenCircuits.Complexity.CNFEncoding

/-! Concrete count-preserving compilation of actual finite-TM2 verifiers to CNF.
Machine-running-time certification of the emitter is a separate remaining theorem;
this module does not label the construction a polynomial-time reduction. -/
namespace HiddenCircuits.Complexity
namespace VerifierTableau
open TM2BooleanEncoding
variable {v : BitString → Bool}
variable (M : Turing.TM2ComputableInPolyTime id Computability.encodeBool v)
attribute [local instance] Classical.propDecidable

def HasTrueSymbol : Prop :=
  (⟨M.tm.k₁,M.outputAlphabet.invFun true⟩ : (k : M.tm.K) × M.tm.Γ k) ∈ TM2Alphabet.alphabet M.tm

lemma height_positive (x : BitString) (m : ℕ) : 0 < height M x m := by unfold height;omega

noncomputable def outputCell (x : BitString) (m : ℕ) (ht : HasTrueSymbol M) : Cell M.tm (height M x m) :=
  Sum.inr ⟨M.tm.k₁,(⟨0,height_positive M x m⟩,some ⟨M.outputAlphabet.invFun true,ht⟩)⟩

noncomputable def outputWire (x : BitString) (m : ℕ) (ht : HasTrueSymbol M) : Fin (bitCount M.tm (height M x m)) :=
  cellEnumeration M.tm (height M x m) (outputCell M x m ht)

lemma outputCell_value (x : BitString) (m : ℕ) (ht : HasTrueSymbol M) (b : Bool) :
    encode M.tm (height M x m) (output M b) (outputCell M x m ht) = b := by
  classical
  cases b <;> simp [encode,outputCell,output,Turing.haltList,Computability.encodeBool]

lemma finalNetwork_code (x : BitString) (m : ℕ) (w : Fin m → Bool) :
    ((network M.tm (height M x m)).step)^[horizon M x m]
      (encodeFin M.tm (height M x m) (initial M x w)) =
    encodeFin M.tm (height M x m) (output M (v (pairBits x (List.ofFn w)))) := by
  have h := network_iterate_input M.tm ((pairBits x (List.ofFn w)).map M.inputAlphabet.invFun)
    (horizon M x m) (horizon M x m) le_rfl
  rw [show ((pairBits x (List.ofFn w)).map M.inputAlphabet.invFun).length = 2*x.length+m+1 by simp] at h
  change ((network M.tm (height M x m)).step)^[horizon M x m]
    (encodeFin M.tm (height M x m) (initial M x w)) =
    encodeFin M.tm (height M x m) ((stutter M.tm.step)^[horizon M x m] (initial M x w)) at h
  rw [final_output M x w] at h
  exact h

lemma finalNetwork_value (x : BitString) (m : ℕ) (ht : HasTrueSymbol M) (w : Fin m → Bool) :
    (((network M.tm (height M x m)).step)^[horizon M x m]
      (InitialNetwork.initial (sources M x m) w)) (outputWire M x m ht) =
    v (pairBits x (List.ofFn w)) := by
  rw [sources_correct M x m w,finalNetwork_code M x m w]
  simpa [encodeFin,outputWire] using outputCell_value M x m ht (v (pairBits x (List.ofFn w)))

noncomputable def positiveFormula (x : BitString) (m : ℕ) (ht : HasTrueSymbol M) :=
  InitialNetwork.toCNF (network M.tm (height M x m)) (horizon M x m)
    (sources M x m) (outputWire M x m ht)

theorem positiveFormula_count (x : BitString) (m : ℕ) (ht : HasTrueSymbol M) :
    (positiveFormula M x m ht).satCount = certificateCount v x m := by
  classical
  unfold positiveFormula
  rw [InitialNetwork.toCNF_count]
  unfold certificateCount
  conv_rhs => rw [← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun w => by rw [finalNetwork_value M x m ht w])

/-- If the true symbol cannot occur in the actual alphabet, there are no accepted certificates. -/
theorem no_true_symbol_count (x : BitString) (m : ℕ) (ht : ¬ HasTrueSymbol M) :
    certificateCount v x m = 0 := by
  classical
  unfold certificateCount
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun w => ?_⟩
  have hc := finalOutput_valid M x w.val
  rw [w.property] at hc
  apply ht
  apply hc.1 M.tm.k₁ (M.outputAlphabet.invFun true)
  simp [output,Turing.haltList,Computability.encodeBool]

end VerifierTableau

def rejectingCNF (inputs : ℕ) : CNF inputs 1 := ⟨fun _ => []⟩

theorem rejectingCNF_count (inputs : ℕ) : (rejectingCNF inputs).satCount = 0 := by
  classical
  unfold CNF.satCount
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun w => ?_⟩
  have h := w.property 0
  simpa [rejectingCNF,CNF.ClauseSatisfied] using h

namespace VerifierTableau
variable {v : BitString → Bool}
variable (M : Turing.TM2ComputableInPolyTime id Computability.encodeBool v)

/-- The actual CNF instance, including the degenerate always-rejecting case. -/
noncomputable def formula (x : BitString) (m : ℕ) : CNFInput := by
  classical
  exact if ht : HasTrueSymbol M then ⟨_,_,positiveFormula M x m ht⟩ else ⟨m,1,rejectingCNF m⟩

lemma formula_pos (x : BitString) (m : ℕ) (ht : HasTrueSymbol M) :
    formula M x m = ⟨_,_,positiveFormula M x m ht⟩ := by
  unfold formula
  exact dif_pos ht

lemma formula_neg (x : BitString) (m : ℕ) (ht : ¬ HasTrueSymbol M) :
    formula M x m = ⟨m,1,rejectingCNF m⟩ := by
  unfold formula
  exact dif_neg ht

/-- Exact counting correctness of the full, concrete machine-to-CNF construction. -/
theorem formula_count (x : BitString) (m : ℕ) :
    (formula M x m).2.2.satCount = certificateCount v x m := by
  classical
  by_cases ht : HasTrueSymbol M
  · rw [formula_pos M x m ht]
    exact positiveFormula_count M x m ht
  · rw [formula_neg M x m ht]
    exact (rejectingCNF_count m).trans (no_true_symbol_count M x m ht).symm

end VerifierTableau

/-- Count preservation is proved for every genuine #P verifier. Polynomial-size
and polynomial-time emitter theorems must be supplied separately before hardness. -/
theorem SharpP.exists_count_preserving_cnf {f : BitString → ℕ} (hf : SharpP f) :
    ∃ F : BitString → CNFInput, ∀ x, (F x).2.2.satCount = f x := by
  obtain ⟨p,v,⟨M⟩,hc⟩ := hf
  exact ⟨fun x => VerifierTableau.formula M x (p.eval x.length),fun x =>
    (VerifierTableau.formula_count M x _).trans (hc x).symm⟩

end HiddenCircuits.Complexity
