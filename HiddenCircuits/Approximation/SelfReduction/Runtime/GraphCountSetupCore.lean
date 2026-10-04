import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountSetup
import HiddenCircuits.Approximation.SelfReduction.Runtime.CountSetupCore

/-! Exact seventy-three-stack handoff from graph parsing to the count core. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountSetup
open Complexity OracleBlock GraphVerifier GraphReduction Polynomial
set_option maxHeartbeats 1500000

/-- Both loop depth and original depth equal half the original graph order. -/
theorem output_core (raw : BitString) (G : GraphInput) (he : GraphInput.decode (graph raw)=some G) :
    Function.update (output raw) (69:Fin 73) [] =
      coreStore (countStore (coins raw) [] (graph raw)
        (SelfReduction.GraphCount.uniformSampleBitsPolynomial.eval (size raw))
        (batchSize (uniformAccuracy (size raw))) (uniformAccuracy (size raw))
        (size raw+1) (2*uniformConfidence (size raw)+2) (G.1/2) [] [true] 0 0) (G.1/2) (size raw) := by
  have hd := dimension_of_decode he
  funext i
  fin_cases i <;> simp [output,hCleared,guarded,generated,depthCopied,halved,validatedClean,parsed,
    coreStore,countStore,countFrame,stageStore,parameterPolynomial,uniformAccuracy,uniformConfidence,
    batchSize,hd,depth,Fin.addCases,Fin.cases]
  all_goals first | rfl | omega

@[simp] lemma output_gate (raw : BitString) : output raw 69=[ready raw] := rfl

export CountSetup (reject rejectTime reject_executes reject_queryFree)

/-- Rejection produces exactly the canonical zero rational output. -/
theorem reject_setup_output (g : BitString → ℕ) (raw : BitString) :
    ∃c,reject.Executes g (output raw)
      (Function.update (fun _ : Fin 73 => ([]:BitString)) 0 (encodeRatio 0 0)) c ∧
      c≤(rejectTime.comp (X+time)).eval raw.length := by
  simpa [encodeRatio] using reject_executes g (output raw) (raw.length+time.eval raw.length)
    (program_storage g raw)

end HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountSetup
