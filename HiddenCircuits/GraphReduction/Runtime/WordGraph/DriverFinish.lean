import HiddenCircuits.GraphReduction.Runtime.WordGraph.DriverState
import HiddenCircuits.Complexity.BinaryArithmetic.Operations

/-! Fresh reconstruction of exact signed division and physical cleanup of the
98-stack interpolation driver. Divisibility is proved by the recovery algebra. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.Driver
open Complexity OracleBlock BinaryArithmetic Polynomial
set_option maxHeartbeats 600000

def finishEmbedding : Fin 9 ↪ Fin 98 where
  toFun i := ![10,11,16,17,18,19,20,21,22] i
  inj' := by decide +kernel
noncomputable def finish : OracleBlock 97 := seq (rename Operation.divide.program finishEmbedding)
  (cleanResult 10 16 (by decide) (by decide))
noncomputable def finishTime : Polynomial ℕ :=
  operationTime.comp (2*X)+102*(X+operationTime.comp (2*X)+3)+3

theorem finish_executes (g : BitString → ℕ) (w : WordInstance) (k t h l s : ℕ)
    (a : ℤ×ℤ) (N : ℕ) (hn : a.2≠0) (hd : a.2∣a.1)
    (hs : ∀i,(state w k t h l s a [] [] [] i).length≤N) :
    ∃c,finish.Executes g (state w k t h l s a [] [] [])
      (Function.update (fun _ => []) 0 (signedBits (a.1/a.2))) c ∧ c≤finishTime.eval N := by
  let start := state w k t h l s a [] [] []
  obtain ⟨c,hc,hcb⟩ := Operation.divide.executes g a.1 a.2 ⟨hn,hd⟩
  have hop := rename_binary_executes Operation.divide.program finishEmbedding g start
    (signedBits a.1) (signedBits a.2) (signedBits (a.1/a.2)) c hc
    (by funext i;fin_cases i <;> rfl)
  let final := Function.update (Function.update start (finishEmbedding 0) (signedBits (a.1/a.2))) (finishEmbedding 1) []
  obtain ⟨d,hd,hdb⟩ := cleanResult_executes g (10:Fin 98) 16 (by decide) (by decide) (by decide)
    final (N+c) (hop.stack_bound hs)
  have hv : final 10=signedBits (a.1/a.2) := rfl
  rw [hv] at hd
  refine ⟨c+d+2,seq_executes _ _ g hop hd,?_⟩
  have h0 := hs 10
  have h1 := hs 11
  change (signedBits a.1).length≤N at h0
  change (signedBits a.2).length≤N at h1
  have hp := polynomial_nat_eval_mono operationTime (show (signedBits a.1).length+(signedBits a.2).length≤2*N by omega)
  dsimp only at hp
  simp only [finishTime,eval_add,eval_mul,eval_comp,eval_X,eval_ofNat]
  omega
lemma finish_queryFree : finish.QueryFree := seq_queryFree _ _
  (rename_queryFree _ _ Operation.divide.queryFree) (cleanResult_queryFree _ _ _ _)
end HiddenCircuits.GraphReduction.Runtime.WordGraph.Driver
