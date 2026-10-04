import HiddenCircuits.Circuit.Runtime.ConstraintSourceFinishCore

namespace HiddenCircuits.Circuit.Runtime.ConstraintSource
open Complexity OracleBlock BinaryArithmetic Polynomial
set_option maxHeartbeats 1200000

lemma quotient_executes (g : BitString→ℕ) (a n f z count B : ℕ) (u : ℤ)
    (hu : u=(count:ℤ)*(2:ℤ)^(3*a))
    (hB : ∀i,((finishStore (pairBits (signedBits u) (signedBits 1)) a n f z) i).length ≤ B) :
    ∃c,quotient.Executes g (finishStore (pairBits (signedBits u) (signedBits 1)) a n f z)
      (finishStore [] a n f z (Computability.encodeNat count) [] [false] (signedBits 1)) c ∧
      c ≤ quotientTime.eval B := by
  obtain ⟨d,hd,hdb⟩:=denominator_executes g a n f z u
  have ha : a ≤ B := by simpa [finishStore] using hB 1
  have hraw : (pairBits (signedBits u) (signedBits 1)).length ≤ B := hB 0
  have hnum : (signedBits u).length ≤ B := by rw [pairBits_length] at hraw;omega
  have hdTime : d ≤ denominatorTime.eval B := by
    simp only [denominatorTime,eval_add,eval_mul,eval_ofNat,eval_X];omega
  obtain ⟨v,hv,hvb⟩:=divide_executes g a n f z count u hu
  have hst:=hd.stack_bound hB
  have hn : (signedBits u).length ≤ B+d := hst (11:Fin 36)
  have hden : (signedBits ((2:ℤ)^(3*a))).length ≤ B+d := hst (12:Fin 36)
  have hm:=polynomial_nat_eval_mono FinalCountRuntime.time (show
    (signedBits u).length+(signedBits ((2:ℤ)^(3*a))).length ≤ 2*(B+denominatorTime.eval B) by omega)
  dsimp only at hm
  refine ⟨d+v+2,seq_executes _ _ g hd hv,?_⟩
  simp only [quotientTime,eval_add,eval_comp,eval_mul,eval_ofNat,eval_X]
  omega

lemma finish_executes (g : BitString→ℕ) (a n f z count B : ℕ) (u : ℤ)
    (hu : u=(count:ℤ)*(2:ℤ)^(3*a))
    (hB : ∀i,((finishStore (pairBits (signedBits u) (signedBits 1)) a n f z) i).length ≤ B) :
    ∃c,finish.Executes g (SourceMetadata.outputStore (pairBits (signedBits u) (signedBits 1)) a n f z)
      (Function.update (fun _ : Fin 36=>[]) 0 (Computability.encodeNat count)) c ∧ c ≤ finishTime.eval B := by
  obtain ⟨c,hc,hcb⟩:=quotient_executes g a n f z count B u hu hB
  obtain ⟨d,hd,hdb⟩:=cleanResult_executes g (11:Fin 36) 24 (by decide) (by decide) (by decide)
    (finishStore [] a n f z (Computability.encodeNat count) [] [false] (signedBits 1)) (B+c) (hc.stack_bound hB)
  have he:=seq_executes _ _ g hc hd
  rw [initial_finishStore] at he
  refine ⟨c+d+2,he,?_⟩
  simp only [finishTime,eval_add,eval_mul,eval_ofNat,eval_X]
  omega
end HiddenCircuits.Circuit.Runtime.ConstraintSource
