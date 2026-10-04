import HiddenCircuits.Approximation.SelfReduction.Runtime.FirstPartner
import HiddenCircuits.Approximation.SamplerRuntime.Output

/-! Total clean execution and canonical sound-witness semantics for the
first-partner decoder, including failure and malformed strings. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock GraphVerifier
open GraphVerifier.Runtime

 theorem parseStore_update_source (raw word tmp flag new : BitString) :
    Function.update (parseStore raw word tmp flag) (0 : Fin 4) new = parseStore new word tmp flag := by
  funext i; fin_cases i <;> rfl

 theorem firstPartner_clear (g : BitString → ℕ) (raw : BitString) :
    (clear (0 : Fin 4)).Executes g (parseStore raw [] [] []) (parseStore [] [] [] []) (raw.length+1) := by
  simpa only [parseStore_update_source] using clear_executes g (0 : Fin 4) (parseStore raw [] [] [])

 theorem firstPartnerWord_executes (g : BitString → ℕ) (raw : BitString) :
    ∃ t, firstPartnerWord.Executes g (parseStore raw [] [] [])
      (parseStore (firstPartnerValue raw) [] [] []) t ∧ t ≤ 20*raw.length+34 := by
  cases raw with
  | nil => exact ⟨3,firstPartnerWord_empty g,by simp⟩
  | cons bit rest =>
    cases bit with
    | false =>
      refine ⟨rest.length+3,?_,by simp; omega⟩
      apply branchPop_false _ _ _ _ g rfl
      simpa only [parseStore_update_source] using firstPartner_clear g rest
    | true =>
      cases rest with
      | nil =>
        refine ⟨5,?_,by simp⟩
        apply branchPop_true _ _ _ _ g rfl
        rw [parseStore_update_source]
        apply branchPop_empty _ _ _ _ g rfl
        exact firstPartner_clear g []
      | cons bit tail =>
        cases bit with
        | false =>
          refine ⟨tail.length+5,?_,by simp; omega⟩
          apply branchPop_true _ _ _ _ g rfl
          rw [parseStore_update_source]
          apply branchPop_false _ _ _ _ g rfl
          simpa only [parseStore_update_source] using firstPartner_clear g tail
        | true =>
          obtain ⟨t,ht,hb⟩ := firstPartnerRead_executes g tail
          refine ⟨t+4,?_,by simp; omega⟩
          apply branchPop_true _ _ _ _ g rfl
          rw [parseStore_update_source]
          apply branchPop_true _ _ _ _ g rfl
          simpa only [parseStore_update_source] using ht

 theorem firstPartnerWord_clean (g : BitString → ℕ) (raw : BitString) :
    ∃ t, firstPartnerWord.Executes g (Function.update (fun _ => []) 0 raw)
      (Function.update (fun _ => []) 0 (firstPartnerValue raw)) t ∧ t ≤ 20*raw.length+34 := by
  have hc (x : BitString) : parseStore x [] [] []=Function.update (fun _ => []) 0 x := by
    funext i; fin_cases i <;> rfl
  simpa only [hc] using firstPartnerWord_executes g raw

@[simp] theorem firstPartnerValue_success (word : BitString) (rest : List BitString) :
    firstPartnerValue (true::encodeBitList (word::rest))=true::word := by
  simp [encodeBitList,firstPartnerValue,parse_pair]

@[simp] theorem firstPartnerValue_empty : firstPartnerValue []=[] := rfl

 theorem firstPartnerValue_witness {n : ℕ} (π : Equiv.Perm (Fin (n+1))) :
    firstPartnerValue (SamplerRuntime.Output.success π)=true::List.replicate (π 0).val true := by
  simp only [SamplerRuntime.Output.success,SamplerRuntime.Output.witness,
    SamplerRuntime.Switch.rowWords,GraphReduction.MonotoneEndpointEncoding.rows,List.ofFn_succ]
  exact firstPartnerValue_success _ _

 theorem firstPartnerWord_queryFree : firstPartnerWord.QueryFree := by
  have ha : firstPartnerAccept.QueryFree := seq_queryFree _ _ (clear_queryFree _)
    (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _) (push_queryFree _ _))
  have hr : firstPartnerReject.QueryFree := seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _)
  have hp : firstPartnerRead.QueryFree := seq_queryFree _ _ unpairBlock_queryFree
    (branchPop_queryFree _ _ _ _ hr hr ha)
  exact branchPop_queryFree _ _ _ _ (clear_queryFree _) (clear_queryFree _)
    (branchPop_queryFree _ _ _ _ (clear_queryFree _) (clear_queryFree _) hp)

end HiddenCircuits.Approximation.SelfReduction.Runtime
