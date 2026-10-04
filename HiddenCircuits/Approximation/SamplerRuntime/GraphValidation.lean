import HiddenCircuits.Approximation.SamplerRuntime.GraphValidationInput
import HiddenCircuits.Complexity.OracleIrrelevance

/-! Fresh reconstruction: literal all-input graph validity is computed by the
already verified finite graph verifier, with a constructed zero witness. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.GraphParser
open Complexity OracleBlock GraphVerifier GraphVerifier.Runtime Polynomial
set_option maxHeartbeats 800000

noncomputable def validationCore : OracleBlock 37 := seq verifierBlock (cleanup 0)
noncomputable def validationCoreTime : Polynomial ℕ := 1000*(X+1)^4+38*(X+1000*(X+1)^4+3)+3
lemma validationCore_queryFree : validationCore.QueryFree := seq_queryFree _ _ verifierBlock_queryFree (cleanup_queryFree _)
lemma validationCore_executes (g : BitString → ℕ) (xs : BitString) :
    ∃c,validationCore.Executes g (Function.update (fun _ => []) 0 xs)
      (Function.update (fun _ => []) 0 [verifier xs]) c ∧ c≤validationCoreTime.eval xs.length := by
  obtain ⟨s,c,hc,ho,hcb⟩ := verifierBlock_executes xs
  have hi : ∀i,(Function.update (fun _ : Fin 38 => ([]:BitString)) 0 xs i).length≤xs.length := by
    intro i
    by_cases h:i=0
    · subst i;exact le_rfl
    · rw [Function.update_of_ne h];exact Nat.zero_le _
  obtain ⟨d,hd,hdb⟩ := cleanup_executes (fun _ => 0) (0:Fin 38) s (xs.length+c) (hc.stack_bound hi)
  rw [ho] at hd
  have hh := seq_executes _ _ (fun _ => 0) hc hd
  refine ⟨c+d+2,Executes.changeOracle validationCore_queryFree g hh,?_⟩
  simp only [validationCoreTime,eval_add,eval_mul,eval_pow,eval_X,eval_one,eval_ofNat]
  omega

def validationEmbedding : Fin 38 ↪ Fin 39 where
  toFun i := ⟨i.val+1,by omega⟩
  inj' := by intro i j h;apply Fin.ext;have hh:=congrArg (fun q : Fin 39 => q.val) h;dsimp at hh;omega
noncomputable def validate : OracleBlock 38 := seq prepareValidation (rename validationCore validationEmbedding)
noncomputable def validationTime : Polynomial ℕ := 23*X+22+validationCoreTime.comp (3*X+1)

theorem validate_executes (g : BitString → ℕ) (raw : BitString) :
    ∃c,validate.Executes g (validationStore raw [] [] [])
      (validationStore raw [(GraphInput.decode raw).isSome] [] []) c ∧ c≤validationTime.eval raw.length := by
  have h1 := prepareValidation_executes g raw
  obtain ⟨c,hc,hcb⟩ := validationCore_executes g (validationInput raw)
  rw [validation_correct] at hc
  have h2 : (rename validationCore validationEmbedding).Executes g
      (validationStore raw (validationInput raw) [] [])
      (validationStore raw [(GraphInput.decode raw).isSome] [] []) c := by
    apply rename_executes_to _ validationEmbedding g hc
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi
      have h1 : i.val≠1 := fun h => hi 0 (Fin.ext h.symm)
      simp only [validationStore,h1,if_false]
  refine ⟨_,seq_executes _ _ g h1 h2,?_⟩
  rw [validationInput_length] at hcb
  simp only [validationTime,eval_add,eval_mul,eval_comp,eval_X,eval_one,eval_ofNat]
  omega
lemma validate_queryFree : validate.QueryFree := seq_queryFree _ _ prepareValidation_queryFree
  (rename_queryFree _ _ validationCore_queryFree)
end HiddenCircuits.Approximation.SamplerRuntime.GraphParser
