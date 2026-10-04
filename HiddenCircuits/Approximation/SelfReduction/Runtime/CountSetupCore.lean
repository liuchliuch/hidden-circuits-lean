import HiddenCircuits.Approximation.SelfReduction.Runtime.CountSetup
import HiddenCircuits.Approximation.SelfReduction.Runtime.CountCoreFrame

/-! Clean count-loop handoff and explicitly charged malformed-input rejection. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.CountSetup
open Complexity OracleBlock GraphVerifier GraphReduction Polynomial
set_option maxHeartbeats 1500000

/-- The input after consuming the setup decision bit agrees literally with the
73-stack counting core. The original dimension and request size are retained. -/
theorem output_core (raw : BitString) (E : MonotoneEndpointEncoding.Input)
    (he : MonotoneEndpointEncoding.decode (graph raw)=some E) :
    Function.update (output raw) (69:Fin 73) [] =
      coreStore (countStore (coins raw) [] (graph raw)
        (SelfReduction.EndpointResidual.uniformSampleBitsPolynomial.eval (size raw))
        (batchSize (uniformAccuracy (size raw))) (uniformAccuracy (size raw))
        (size raw+1) (2*uniformConfidence (size raw)+2) E.1 [] [true] 0 0) E.1 (size raw) := by
  have hd : dimension raw=List.replicate E.1 true :=
    (SamplerRuntime.EndpointParser.fields_of_decode he).1
  funext i
  fin_cases i <;> simp [output,hCleared,guarded,generated,depthCopied,validatedClean,parsed,
    coreStore,countStore,countFrame,stageStore,parameterPolynomial,uniformAccuracy,uniformConfidence,
    batchSize,hd,Fin.addCases,Fin.cases]
  all_goals first | rfl | omega

@[simp] lemma output_gate (raw : BitString) : output raw 69=[ready raw] := rfl

noncomputable def reject : OracleBlock 72 := seq (clearList (List.finRange 73)) (push 0 false)
noncomputable def rejectTime : Polynomial ℕ := 73*(X+3)+4

theorem reject_executes (g : BitString → ℕ) (s : Store 72) (B : ℕ)
    (hs : ∀i,(s i).length≤B) :
    ∃c,reject.Executes g s (Function.update (fun _ : Fin 73 => ([]:BitString)) 0 [false]) c ∧
      c≤rejectTime.eval B := by
  obtain ⟨c,hc,hb⟩ := clearList_executes g (List.finRange 73) s B hs
  have he : eraseStore (List.finRange 73) s=(fun _ : Fin 73 => ([]:BitString)) := by
    funext i;simp [eraseStore]
  rw [he] at hc
  refine ⟨_,seq_executes _ _ g hc (push_executes g (0:Fin 73) false (fun _ : Fin 73 => ([]:BitString))),?_⟩
  simpa [rejectTime] using Nat.add_le_add_right (by simpa using hb) 3
lemma reject_queryFree : reject.QueryFree := seq_queryFree _ _ (clearList_queryFree _) (push_queryFree _ _)

/-- Total bad-input cleanup is polynomial in actual raw bytes; no loop receives
a short random tape, invalid syntax, or a failed endpoint-validation flag. -/
theorem reject_setup_output (g : BitString → ℕ) (raw : BitString) :
    ∃c,reject.Executes g (output raw)
      (Function.update (fun _ : Fin 73 => ([]:BitString)) 0 (encodeRatio 0 0)) c ∧
      c≤(rejectTime.comp (X+time)).eval raw.length := by
  simpa [encodeRatio] using reject_executes g (output raw) (raw.length+time.eval raw.length)
    (program_storage g raw)

end HiddenCircuits.Approximation.SelfReduction.Runtime.CountSetup
