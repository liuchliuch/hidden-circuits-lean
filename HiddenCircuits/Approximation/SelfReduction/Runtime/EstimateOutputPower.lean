import HiddenCircuits.Approximation.SelfReduction.Runtime.EstimateOutputProduct
import HiddenCircuits.Complexity.BinaryArithmetic.PowerRuntime

/-! Physical unary-base exponentiation, with the actual binary power loop. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.EstimateOutput
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic Polynomial

 theorem rename_clean_executes {k l : ℕ} (B : OracleBlock k) (φ : Fin (k+1) ↪ Fin (l+1))
    (g : BitString → ℕ) (outer : Store l) (x y : BitString) (t : ℕ)
    (h : B.Executes g (clean x) (clean y) t) (hs : outer ∘ φ=clean x) :
    (rename B φ).Executes g outer (Function.update outer (φ 0) y) t := by
  apply rename_executes_to B φ g h hs
  · funext i
    have hh := congrFun hs i
    change outer (φ i)=clean x i at hh
    by_cases hi : i=0
    · subst i; simp [clean]
    · simp [Function.update_of_ne (φ.injective.ne hi),clean,hi] at hh ⊢
      exact hh
  · intro j hj
    simp [Function.update_of_ne (Ne.symm (hj 0))]

def powerUnaryPorts : Fin 3 ↪ Fin 17 where
  toFun i := ![0,2,3] i
  inj' := by decide +kernel

noncomputable def numerator : OracleBlock 16 := seq (rename unarySigned powerUnaryPorts) PowerRuntime.program
noncomputable def numeratorTime : Polynomial ℕ := unaryTime+PowerRuntime.time.comp (X+1)+2

 theorem numerator_executes (g : BitString → ℕ) (M d : ℕ) :
    ∃ t, numerator.Executes g
      (PowerRuntime.inputStore (List.replicate M true) (List.replicate d true))
      (clean (signedBits ((M^d : ℕ) : ℤ))) t ∧ t≤numeratorTime.eval (M+d) := by
  let s0 := PowerRuntime.inputStore (List.replicate M true) (List.replicate d true)
  let s1 := PowerRuntime.inputStore (signedBits (M : ℤ)) (List.replicate d true)
  obtain ⟨a,ha,hab⟩ := unarySigned_executes g (List.replicate M true)
  simp only [List.length_replicate] at ha hab
  have h₁ : (rename unarySigned powerUnaryPorts).Executes g s0 s1 a := by
    apply rename_executes_to unarySigned powerUnaryPorts g ha
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
    · intro j hj
      have hj0 : j≠0 := by simpa [powerUnaryPorts] using (Ne.symm (hj 0))
      simp [s0,s1,PowerRuntime.inputStore,show j.val≠0 by simpa using hj0]
  obtain ⟨b,hb,hbb⟩ := PowerRuntime.program_executes g (M : ℤ) (List.replicate d true)
  have h₂ : PowerRuntime.program.Executes g s1 (clean (signedBits ((M^d : ℕ) : ℤ))) b := by
    simpa [s1,clean] using hb
  refine ⟨a+b+2,seq_executes _ _ g h₁ h₂,?_⟩
  have hlen : (signedBits (M : ℤ)).length+(List.replicate d true).length≤M+d+1 := by
    simp only [signedBits_nat,List.length_cons,List.length_replicate]
    have := natBits_length M
    omega
  have hb' := hbb.trans (polynomial_nat_eval_mono PowerRuntime.time hlen)
  have ha' := hab.trans (polynomial_nat_eval_mono unaryTime (show M≤M+d by omega))
  dsimp only at ha' hb'
  simp only [numeratorTime,eval_add,eval_comp,eval_X,eval_one,eval_ofNat]
  omega

 theorem numerator_queryFree : numerator.QueryFree := seq_queryFree _ _
  (rename_queryFree _ _ unarySigned_queryFree) PowerRuntime.program_queryFree

end HiddenCircuits.Approximation.SelfReduction.Runtime.EstimateOutput
