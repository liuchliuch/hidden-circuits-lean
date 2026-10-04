import HiddenCircuits.Complexity.BinaryArithmetic.Parity
import HiddenCircuits.Complexity.BinaryArithmetic.InterpolationFormulas
import HiddenCircuits.Complexity.BinaryArithmetic.Division

/-! Finite interpolation-weight arithmetic after factorial generation. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic
open OracleBlock

def denominatorStore (a b result clock : BitString) : Store 6 := fun i =>
  if i.val=0 then a else if i.val=1 then b else if i.val=2 then result else if i.val=6 then clock else []

def denominatorMulEmbedding : Fin 6 ↪ Fin 7 where
  toFun i := i.castLE (by decide)
  inj' := by intro i j h; exact Fin.ext (congrArg (fun x : Fin 7 => x.val) h)

def denominatorParityEmbedding : Fin 2 ↪ Fin 7 where
  toFun i := if i.val=0 then 6 else 0
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

noncomputable def denominatorMultiply : OracleBlock 6 := rename multiplicationBlock denominatorMulEmbedding
noncomputable def denominatorParity : OracleBlock 6 := rename parityBlock denominatorParityEmbedding
noncomputable def denominatorCombine : OracleBlock 6 :=
  seq denominatorMultiply (seq denominatorParity (seq (finishFrom 0 2) (clear 1)))

/-- Two factorial magnitudes and the unary sign clock are combined by actual
binary multiplication, unary parity, and canonical sign writing. -/
theorem denominatorCombine_executes (g : BitString → ℕ) (i k : ℕ) :
    ∃ t, denominatorCombine.Executes g
      (denominatorStore (Computability.encodeNat i.factorial) (Computability.encodeNat k.factorial) [] (List.replicate k true))
      (denominatorStore [] [] (signedBits ((-1 : ℤ)^k*(i.factorial : ℤ)*(k.factorial : ℤ))) []) t ∧
      t ≤ 18+2*(Computability.encodeNat i.factorial).length+
        (Computability.encodeNat i.factorial).length*
          (5*((Computability.encodeNat i.factorial).length*((Computability.encodeNat k.factorial).length+2))+
            10*(Computability.encodeNat k.factorial).length+22)+k+(Computability.encodeNat k.factorial).length := by
  obtain ⟨t,ht,hbound⟩ := multiply_binary_output g i.factorial k.factorial
  have hm : denominatorMultiply.Executes g
      (denominatorStore (Computability.encodeNat i.factorial) (Computability.encodeNat k.factorial) [] (List.replicate k true))
      (denominatorStore [] (Computability.encodeNat k.factorial) (Computability.encodeNat (i.factorial*k.factorial))
        (List.replicate k true)) t := by
    apply rename_executes_to multiplicationBlock denominatorMulEmbedding g ht
    · funext j; fin_cases j <;> rfl
    · funext j; fin_cases j <;> rfl
    · intro j hj
      fin_cases j
      · exact False.elim (hj 0 rfl)
      · rfl
      · exact False.elim (hj 2 rfl)
      · rfl
      · rfl
      · rfl
      · rfl
  have hp : denominatorParity.Executes g
      (denominatorStore [] (Computability.encodeNat k.factorial) (Computability.encodeNat (i.factorial*k.factorial))
        (List.replicate k true))
      (denominatorStore [parityBit k] (Computability.encodeNat k.factorial)
        (Computability.encodeNat (i.factorial*k.factorial)) []) (k+2) := by
    have h := parityBlock_executes g (List.replicate k true) []
    simp only [List.length_replicate] at h
    apply rename_executes_to parityBlock denominatorParityEmbedding g h
    · funext j; fin_cases j <;> rfl
    · funext j; fin_cases j <;> rfl
    · intro j hj
      fin_cases j
      · exact False.elim (hj 1 rfl)
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact False.elim (hj 0 rfl)
  have hs : (finishFrom (0 : Fin 7) 2).Executes g
      (denominatorStore [parityBit k] (Computability.encodeNat k.factorial)
        (Computability.encodeNat (i.factorial*k.factorial)) [])
      (denominatorStore [] (Computability.encodeNat k.factorial)
        (signedBits ((-1 : ℤ)^k*(i.factorial : ℤ)*(k.factorial : ℤ))) [])
      (finishCost (Computability.encodeNat (i.factorial*k.factorial))+2) := by
    convert finishFrom_executes g (0 : Fin 7) 2 (by decide)
      (denominatorStore [parityBit k] (Computability.encodeNat k.factorial)
        (Computability.encodeNat (i.factorial*k.factorial)) []) (parityBit k) rfl using 1
    funext j; fin_cases j <;> first | rfl | (symm; simpa [Nat.cast_mul,mul_assoc] using finishSigned_parity k (i.factorial*k.factorial))
  have hc : (clear (1 : Fin 7)).Executes g
      (denominatorStore [] (Computability.encodeNat k.factorial)
        (signedBits ((-1 : ℤ)^k*(i.factorial : ℤ)*(k.factorial : ℤ))) [])
      (denominatorStore [] [] (signedBits ((-1 : ℤ)^k*(i.factorial : ℤ)*(k.factorial : ℤ))) [])
      ((Computability.encodeNat k.factorial).length+1) := by
    convert clear_executes g (1 : Fin 7)
      (denominatorStore [] (Computability.encodeNat k.factorial)
        (signedBits ((-1 : ℤ)^k*(i.factorial : ℤ)*(k.factorial : ℤ))) []) using 1
    funext j; fin_cases j <;> rfl
  have h := seq_executes _ _ g hm (seq_executes _ _ g hp (seq_executes _ _ g hs hc))
  refine ⟨_,h,?_⟩
  have hf := finishCost_le (Computability.encodeNat (i.factorial*k.factorial))
  omega

theorem denominatorCombine_correct (g : BitString → ℕ) (d : ℕ) (i : Fin (d+1)) :
    ∃ t, denominatorCombine.Executes g
      (denominatorStore (Computability.encodeNat i.val.factorial)
        (Computability.encodeNat (d-i.val).factorial) [] (List.replicate (d-i.val) true))
      (denominatorStore [] [] (signedBits (interpolationDenominator d i)) []) t := by
  obtain ⟨t,ht,_⟩ := denominatorCombine_executes g i.val (d-i.val)
  exact ⟨t,by simpa [interpolationDenominator_factorial] using ht⟩

lemma denominatorCombine_queryFree : denominatorCombine.QueryFree :=
  seq_queryFree _ _ (rename_queryFree _ _ multiplicationBlock_queryFree)
    (seq_queryFree _ _ (rename_queryFree _ _ parityBlock_queryFree)
      (seq_queryFree _ _ (finishFrom_queryFree _ _) (clear_queryFree _)))

def numeratorStore (a b r q clock : BitString) : Store 9 := fun i =>
  if i.val=0 then a else if i.val=1 then b else if i.val=2 then r else if i.val=3 then q
  else if i.val=9 then clock else []

def numeratorDivEmbedding : Fin 9 ↪ Fin 10 where
  toFun i := i.castLE (by decide)
  inj' := by intro i j h; exact Fin.ext (congrArg (fun x : Fin 10 => x.val) h)

def numeratorParityEmbedding : Fin 2 ↪ Fin 10 where
  toFun i := if i.val=0 then 9 else 0
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

noncomputable def numeratorDivide : OracleBlock 9 := rename divisionBlock numeratorDivEmbedding
noncomputable def numeratorParity : OracleBlock 9 := rename parityBlock numeratorParityEmbedding
noncomputable def numeratorCombine : OracleBlock 9 :=
  seq numeratorDivide (seq numeratorParity (seq (finishFrom 0 3) (clear 1)))

/-- Exact factorial quotient and sign, all executed by finite bit instructions. -/
theorem numeratorCombine_executes (g : BitString → ℕ) (d : ℕ) (i : Fin (d+1)) :
    ∃ t, numeratorCombine.Executes g
      (numeratorStore (Computability.encodeNat (d+1).factorial) (Computability.encodeNat (i.val+1)) [] [] (List.replicate d true))
      (numeratorStore [] [] [] (signedBits (interpolationNegativeNumerator d i)) []) t ∧
      t ≤ (Computability.encodeNat (d+1).factorial).length*(25*(Computability.encodeNat (i.val+1)).length+54)+
        d+(Computability.encodeNat (i.val+1)).length+18 := by
  obtain ⟨t,ht,hbound⟩ := exact_divide_binary_output g (d+1).factorial (i.val+1) (by omega)
    (interpolationNegativeNumerator_divisible d i)
  have hm : numeratorDivide.Executes g
      (numeratorStore (Computability.encodeNat (d+1).factorial) (Computability.encodeNat (i.val+1)) [] [] (List.replicate d true))
      (numeratorStore [] (Computability.encodeNat (i.val+1)) []
        (Computability.encodeNat ((d+1).factorial/(i.val+1))) (List.replicate d true)) t := by
    apply rename_executes_to divisionBlock numeratorDivEmbedding g ht
    · funext j; fin_cases j <;> rfl
    · funext j; fin_cases j <;> rfl
    · intro j hj
      fin_cases j
      · exact False.elim (hj 0 rfl)
      · rfl
      · rfl
      · exact False.elim (hj 3 rfl)
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
  have hp : numeratorParity.Executes g
      (numeratorStore [] (Computability.encodeNat (i.val+1)) []
        (Computability.encodeNat ((d+1).factorial/(i.val+1))) (List.replicate d true))
      (numeratorStore [parityBit d] (Computability.encodeNat (i.val+1)) []
        (Computability.encodeNat ((d+1).factorial/(i.val+1))) []) (d+2) := by
    have h := parityBlock_executes g (List.replicate d true) []
    simp only [List.length_replicate] at h
    apply rename_executes_to parityBlock numeratorParityEmbedding g h
    · funext j; fin_cases j <;> rfl
    · funext j; fin_cases j <;> rfl
    · intro j hj
      fin_cases j
      · exact False.elim (hj 1 rfl)
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact False.elim (hj 0 rfl)
  have hs : (finishFrom (0 : Fin 10) 3).Executes g
      (numeratorStore [parityBit d] (Computability.encodeNat (i.val+1)) []
        (Computability.encodeNat ((d+1).factorial/(i.val+1))) [])
      (numeratorStore [] (Computability.encodeNat (i.val+1)) []
        (signedBits (interpolationNegativeNumerator d i)) [])
      (finishCost (Computability.encodeNat ((d+1).factorial/(i.val+1)))+2) := by
    convert finishFrom_executes g (0 : Fin 10) 3 (by decide)
      (numeratorStore [parityBit d] (Computability.encodeNat (i.val+1)) []
        (Computability.encodeNat ((d+1).factorial/(i.val+1))) []) (parityBit d) rfl using 1
    funext j; fin_cases j <;> first | rfl |
      (symm; simpa [interpolationNegativeNumerator_factorial] using finishSigned_parity d ((d+1).factorial/(i.val+1)))
  have hc : (clear (1 : Fin 10)).Executes g
      (numeratorStore [] (Computability.encodeNat (i.val+1)) []
        (signedBits (interpolationNegativeNumerator d i)) [])
      (numeratorStore [] [] [] (signedBits (interpolationNegativeNumerator d i)) [])
      ((Computability.encodeNat (i.val+1)).length+1) := by
    convert clear_executes g (1 : Fin 10)
      (numeratorStore [] (Computability.encodeNat (i.val+1)) []
        (signedBits (interpolationNegativeNumerator d i)) []) using 1
    funext j; fin_cases j <;> rfl
  have h := seq_executes _ _ g hm (seq_executes _ _ g hp (seq_executes _ _ g hs hc))
  refine ⟨_,h,?_⟩
  have hf := finishCost_le (Computability.encodeNat ((d+1).factorial/(i.val+1)))
  omega

lemma numeratorCombine_queryFree : numeratorCombine.QueryFree :=
  seq_queryFree _ _ (rename_queryFree _ _ divisionBlock_queryFree)
    (seq_queryFree _ _ (rename_queryFree _ _ parityBlock_queryFree)
      (seq_queryFree _ _ (finishFrom_queryFree _ _) (clear_queryFree _)))

end HiddenCircuits.Complexity.BinaryArithmetic
