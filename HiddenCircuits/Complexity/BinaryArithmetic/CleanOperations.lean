import HiddenCircuits.Complexity.BinaryArithmetic.Runtime
import HiddenCircuits.Complexity.BinaryArithmetic.SignedAddition
import HiddenCircuits.Complexity.OracleResult

/-! Clean canonical interfaces for the actual signed arithmetic programs. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic
open OracleBlock Polynomial

noncomputable def cleanMultiply : OracleBlock 5 :=
  cleanBinary signedMultiplicationBlock 2 3 (by decide) (by decide)
noncomputable def cleanDivide : OracleBlock 8 :=
  cleanBinary signedDivisionBlock 3 2 (by decide) (by decide)
noncomputable def cleanMultiplyTime : Polynomial ℕ :=
  integerMultiplicationTime+10*(X+integerMultiplicationTime+3)+3
noncomputable def cleanDivideTime : Polynomial ℕ :=
  integerDivisionTime+13*(X+integerDivisionTime+3)+3

lemma cleanMultiply_executes (g : BitString → ℕ) (a b : ℤ) :
    ∃ t, cleanMultiply.Executes g (binaryStore (signedBits a) (signedBits b))
      (binaryStore (signedBits (a*b)) []) t ∧
      t ≤ cleanMultiplyTime.eval ((signedBits a).length+(signedBits b).length) := by
  obtain ⟨c,hc,hb⟩ := signed_multiply_polynomial g a b
  have hin : mulStore (signedBits a) (signedBits b) [] [] [] [] =
      binaryStore (signedBits a) (signedBits b) := by funext i;fin_cases i <;> rfl
  rw [hin] at hc
  obtain ⟨t,ht,hbound⟩ := cleanBinary_executes signedMultiplicationBlock (2 : Fin 6) 3
    (by decide) (by decide) (by decide) g (signedBits a) (signedBits b) _ (signedBits (a*b)) c hc rfl
  refine ⟨t,ht,hbound.trans ?_⟩
  simp only [cleanMultiplyTime,eval_add,eval_mul,eval_ofNat,eval_X]
  omega

lemma cleanDivide_executes (g : BitString → ℕ) (a b : ℤ) (hb : b≠0) (hd : b∣a) :
    ∃ t, cleanDivide.Executes g (binaryStore (signedBits a) (signedBits b))
      (binaryStore (signedBits (a/b)) []) t ∧
      t ≤ cleanDivideTime.eval ((signedBits a).length+(signedBits b).length) := by
  obtain ⟨c,hc,hbound⟩ := signed_exact_divide_polynomial g a b hb hd
  have hin : divStore (signedBits a) (signedBits b) [] [] [] [] [] [] [] =
      binaryStore (signedBits a) (signedBits b) := by funext i;fin_cases i <;> rfl
  rw [hin] at hc
  obtain ⟨t,ht,htb⟩ := cleanBinary_executes signedDivisionBlock (3 : Fin 9) 2
    (by decide) (by decide) (by decide) g (signedBits a) (signedBits b) _ (signedBits (a/b)) c hc rfl
  refine ⟨t,ht,htb.trans ?_⟩
  simp only [cleanDivideTime,eval_add,eval_mul,eval_ofNat,eval_X]
  omega

noncomputable def cleanAddTime : Polynomial ℕ := 400*(X+1)

lemma cleanAdd_executes (g : BitString → ℕ) (a b : ℤ) :
    ∃ t, signedAddClean.Executes g (binaryStore (signedBits a) (signedBits b))
      (binaryStore (signedBits (a+b)) []) t ∧
      t ≤ cleanAddTime.eval ((signedBits a).length+(signedBits b).length) := by
  obtain ⟨c,hc,hb⟩ := signedAddClean_executes g a b
  have hin : signedAddStore (signedBits a) (signedBits b) [] [] [] [] [] =
      binaryStore (signedBits a) (signedBits b) := by funext i;fin_cases i <;> rfl
  have hout : signedAddStore (signedBits (a+b)) [] [] [] [] [] [] =
      binaryStore (signedBits (a+b)) [] := by funext i;fin_cases i <;> rfl
  rw [hin,hout] at hc
  refine ⟨c,hc,hb.trans ?_⟩
  simp only [cleanAddTime,eval_mul,eval_ofNat,eval_add,eval_X,eval_one,signedBits,List.length_cons]
  omega

lemma cleanMultiply_queryFree : cleanMultiply.QueryFree :=
  seq_queryFree _ _ signedMultiplicationBlock_queryFree (cleanResult_queryFree _ _ _ _)
lemma cleanDivide_queryFree : cleanDivide.QueryFree :=
  seq_queryFree _ _ signedDivisionBlock_queryFree (cleanResult_queryFree _ _ _ _)

end HiddenCircuits.Complexity.BinaryArithmetic
