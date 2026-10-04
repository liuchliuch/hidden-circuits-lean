import HiddenCircuits.GraphReduction.Runtime.WordGraph.EvenWeightsCombine

/-! Both even-node weights are computed from the physical unary index and
complement. Odd factorial, power of two, divisor, sign, and exact division
are all executed by verified finite bit-stack programs. -/
namespace HiddenCircuits.Complexity.EvenWeightsRuntime
open OracleBlock BinaryArithmetic RegisterMachine Polynomial
open HiddenCircuits.GraphReduction
open HiddenCircuits.GraphReduction.Runtime.WordGraph
set_option maxHeartbeats 1000000
noncomputable def program : OracleBlock 30 := seq ordinary (seq fact (seq power (seq divisor (seq sign combine))))
noncomputable def time : Polynomial ℕ := GridWeightsRuntime.pairTime+OddFactorialRuntime.time.comp (X+1)+
  PowerRuntime.time.comp (X+3)+combineTime.comp componentP+200*(X+1)^2

theorem program_executes (g : BitString → ℕ) (d : ℕ) (i : Fin (d+1)) :
    ∃c, program.Executes g (state i.val (d-i.val) [] [] [] [] [] [])
      (state i.val (d-i.val) (signedBits (EvenWeights.denominator d i)) (signedBits (EvenWeights.numerator d i)) [] [] [] []) c ∧
      c ≤ time.eval d := by
  have hi : i.val+(d-i.val)=d := Nat.add_sub_of_le (by omega)
  let den := signedBits (interpolationDenominator d i)
  let f := signedBits (oddFactorial (d+1):ℤ)
  let p := signedBits ((2:ℤ)^d)
  let v := signedBits ((2*i.val+1:ℕ):ℤ)
  obtain ⟨a,ha,hab⟩ := ordinary_executes g d i
  obtain ⟨b,hb,hbb⟩ := fact_executes g i.val (d-i.val) den
  obtain ⟨c,hc,hcb⟩ := power_executes g i.val (d-i.val) den f
  obtain ⟨e,he,heb⟩ := divisor_executes g i.val (d-i.val) den f p
  have hs := sign_executes g i.val (d-i.val) den f p v
  rw [hi] at hb hbb hc hcb hs
  obtain ⟨z,hz,hzb⟩ := combine_executes g i.val (d-i.val) (componentP.eval d)
    (oddFactorial (d+1):ℤ) ((2*i.val+1:ℕ):ℤ) ((-1:ℤ)^d) (interpolationDenominator d i) ((2:ℤ)^d)
    (by simp only [componentP,eval_add,eval_mul,eval_pow,eval_X,eval_ofNat,eval_one];nlinarith [i.isLt])
    (by simp only [componentP,eval_add,eval_mul,eval_pow,eval_X,eval_ofNat,eval_one];nlinarith [Nat.sub_le d i.val])
    (by exact_mod_cast (show 2*i.val+1≠0 by omega))
    (by exact_mod_cast EvenWeights.divisor_dvd d i) (componentBound d i)
  have hnum : (oddFactorial (d+1):ℤ)/((2*i.val+1:ℕ):ℤ)*(-1:ℤ)^d=EvenWeights.numerator d i := by
    rw [EvenWeights.numerator_eq]
    norm_cast
    ring
  have hden : interpolationDenominator d i*(2:ℤ)^d=EvenWeights.denominator d i := by
    unfold EvenWeights.denominator;ring
  rw [hnum,hden] at hz
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb (seq_executes _ _ g hc
    (seq_executes _ _ g he (seq_executes _ _ g hs hz)))),?_⟩
  have heCost : e ≤ (2*d+1)*(4*(2*d+1)+5)+22*d+34 := heb.trans (by gcongr <;> omega)
  simp only [time,eval_add,eval_mul,eval_comp,eval_pow,eval_X,eval_ofNat,eval_one]
  nlinarith

lemma program_queryFree : program.QueryFree := by
  have hsum : sumClock.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (copyOn_queryFree _ _ _ _ _ _)
  have hoc : oddClock.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (push_queryFree _ _))
  have hdc : divisorClock.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (push_queryFree _ _))
  have hpow : powerConstants.QueryFree := seq_queryFree _ _ (push_queryFree _ _)
    (seq_queryFree _ _ (push_queryFree _ _) (push_queryFree _ _))
  exact seq_queryFree _ _ (seq_queryFree _ _ (rename_queryFree _ _ GridWeightsRuntime.pairProgram_queryFree) (clear_queryFree _))
    (seq_queryFree _ _ (seq_queryFree _ _ hoc (seq_queryFree _ _ (rename_queryFree _ _ OddFactorialRuntime.program_queryFree)
      (moveOn_queryFree _ _ _ _ _ _)))
      (seq_queryFree _ _ (seq_queryFree _ _ hsum (seq_queryFree _ _ hpow
        (seq_queryFree _ _ (rename_queryFree _ _ PowerRuntime.program_queryFree) (moveOn_queryFree _ _ _ _ _ _))))
        (seq_queryFree _ _ (seq_queryFree _ _ hdc (seq_queryFree _ _ (rename_queryFree _ _ unaryBinary_queryFree)
          (seq_queryFree _ _ (push_queryFree _ _) (moveOn_queryFree _ _ _ _ _ _))))
          (seq_queryFree _ _ (seq_queryFree _ _ hsum (seq_queryFree _ _ (push_queryFree _ _) (rename_queryFree _ _ parityBlock_queryFree)))
            (seq_queryFree _ _ (seq_queryFree _ _ (push_queryFree _ _) (push_queryFree _ _))
              (seq_queryFree _ _ (rename_queryFree _ _ (compile_queryFree code))
                (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _) (clearList_queryFree _))))))))
end HiddenCircuits.Complexity.EvenWeightsRuntime
