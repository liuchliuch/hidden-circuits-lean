import HiddenCircuits.Complexity.BinaryArithmetic.Factorial
import HiddenCircuits.Complexity.BinaryArithmetic.InterpolationWeightCombine

/-! Actual consecutive-node denominator generation from two unary counts. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic
open OracleBlock OracleMachine

def weightStore (a b c d stash clock : BitString) : Store 9 := fun i =>
  if i.val=0 then a else if i.val=1 then b else if i.val=2 then c else
    if i.val=3 then d else if i.val=8 then stash else if i.val=9 then clock else []

def weightFactorEmbedding (r : Fin 2) : Fin 7 ↪ Fin 10 where
  toFun i := if i=0 then r.castLE (by decide) else ⟨i.val+1,by omega⟩
  inj' := by intro i j h; fin_cases r <;> fin_cases i <;> fin_cases j <;> simp_all

noncomputable def weightFactor (r : Fin 2) : OracleBlock 9 :=
  rename factorialBlock (weightFactorEmbedding r)

 theorem weightFactor_left (g : BitString → ℕ) (xs b stash clock : BitString) :
    ∃ t, (weightFactor 0).Executes g (weightStore xs b [] [] stash clock)
      (weightStore (Computability.encodeNat xs.length.factorial) b [] [] stash clock) t ∧
      t ≤ factorialTime.eval xs.length := by
  obtain ⟨t,ht,hbound⟩ := factorial_polynomial g xs
  refine ⟨t,?_,hbound⟩
  apply rename_executes_to factorialBlock (weightFactorEmbedding 0) g ht
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · intro i hi; fin_cases i <;> first | rfl | (exfalso; exact hi 0 rfl)

 theorem weightFactor_right (g : BitString → ℕ) (xs a stash clock : BitString) :
    ∃ t, (weightFactor 1).Executes g (weightStore a xs [] [] stash clock)
      (weightStore a (Computability.encodeNat xs.length.factorial) [] [] stash clock) t ∧
      t ≤ factorialTime.eval xs.length := by
  obtain ⟨t,ht,hbound⟩ := factorial_polynomial g xs
  refine ⟨t,?_,hbound⟩
  apply rename_executes_to factorialBlock (weightFactorEmbedding 1) g ht
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · intro i hi; fin_cases i <;> first | rfl | (exfalso; exact hi 0 rfl)

def weightDenominatorEmbedding : Fin 7 ↪ Fin 10 where
  toFun i := if i=6 then 9 else i.castLE (by decide)
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

noncomputable def weightDenominatorCombine : OracleBlock 9 :=
  rename denominatorCombine weightDenominatorEmbedding

noncomputable def weightRestore : OracleBlock 9 :=
  seq (reverseOn 2 3 (by decide)) (reverseOn 3 0 (by decide))

 theorem weightRestore_executes (g : BitString → ℕ) (xs : BitString) :
    weightRestore.Executes g (weightStore [] [] xs [] [] [])
      (weightStore xs [] [] [] [] []) (4*xs.length+4) := by
  have h1 : (reverseOn (2 : Fin 10) 3 (by decide)).Executes g
      (weightStore [] [] xs [] [] []) (weightStore [] [] [] xs.reverse [] []) (2*xs.length+1) := by
    convert reverseOn_executes g (2 : Fin 10) 3 (by decide) (weightStore [] [] xs [] [] []) using 1
    funext i; fin_cases i <;> simp [weightStore]
  have h2 : (reverseOn (3 : Fin 10) 0 (by decide)).Executes g
      (weightStore [] [] [] xs.reverse [] []) (weightStore xs [] [] [] [] []) (2*xs.length+1) := by
    convert reverseOn_executes g (3 : Fin 10) 0 (by decide) (weightStore [] [] [] xs.reverse [] []) using 1
    · funext i; fin_cases i <;> simp [weightStore]
    · simp [weightStore]
  convert seq_executes _ _ g h1 h2 using 1 <;> omega

noncomputable def denominatorUnary : OracleBlock 9 :=
  seq (copyOn 1 9 2 (by decide) (by decide) (by decide))
    (seq (weightFactor 0) (seq (weightFactor 1) (seq weightDenominatorCombine weightRestore)))

 theorem factorialTime_mono {m n : ℕ} (h : m ≤ n) : factorialTime.eval m ≤ factorialTime.eval n := by
  simp only [factorialTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_ofNat,Polynomial.eval_one,Polynomial.eval_X]
  gcongr

noncomputable def denominatorUnaryTime : Polynomial ℕ :=
  let L : Polynomial ℕ := (Polynomial.X+1)^2+2
  2*factorialTime+L*(5*(L*(L+2))+10*L+22)+10*L+6*Polynomial.X+40

 theorem denominatorUnary_executes (g : BitString → ℕ) (d : ℕ) (i : Fin (d+1)) :
    ∃ t, denominatorUnary.Executes g
      (weightStore (List.replicate i.val true) (List.replicate (d-i.val) true) [] [] [] [])
      (weightStore (signedBits (interpolationDenominator d i)) [] [] [] [] []) t ∧
      t ≤ denominatorUnaryTime.eval d := by
  let k := d-i.val
  have hc : (copyOn (1 : Fin 10) 9 2 (by decide) (by decide) (by decide)).Executes g
      (weightStore (List.replicate i.val true) (List.replicate k true) [] [] [] [])
      (weightStore (List.replicate i.val true) (List.replicate k true) [] [] [] (List.replicate k true))
      (5*k+2) := by
    convert copyOn_executes g (1 : Fin 10) 9 2 (by decide) (by decide) (by decide)
      (weightStore (List.replicate i.val true) (List.replicate k true) [] [] [] []) rfl using 1
    · funext j; fin_cases j <;> simp [weightStore]
    · simp [weightStore]
  obtain ⟨ta,ha,hba⟩ := weightFactor_left g (List.replicate i.val true) (List.replicate k true) [] (List.replicate k true)
  obtain ⟨tb,hb,hbb⟩ := weightFactor_right g (List.replicate k true) (Computability.encodeNat i.val.factorial) [] (List.replicate k true)
  simp only [List.length_replicate] at ha hb hba hbb
  obtain ⟨tc,htc,hbc⟩ := denominatorCombine_executes g i.val k
  have hd : weightDenominatorCombine.Executes g
      (weightStore (Computability.encodeNat i.val.factorial) (Computability.encodeNat k.factorial) [] [] [] (List.replicate k true))
      (weightStore [] [] (signedBits (interpolationDenominator d i)) [] [] []) tc := by
    apply rename_executes_to denominatorCombine weightDenominatorEmbedding g htc
    · funext j; fin_cases j <;> rfl
    · funext j; fin_cases j <;> first | rfl | (simp [weightStore,denominatorStore,weightDenominatorEmbedding,interpolationDenominator_factorial,k])
    · intro j hj; fin_cases j <;> first | rfl | (exfalso; exact hj 0 rfl) | (exfalso; exact hj 1 rfl) | (exfalso; exact hj 2 rfl) | (exfalso; exact hj 6 rfl)
  refine ⟨_,seq_executes _ _ g hc (seq_executes _ _ g ha (seq_executes _ _ g hb
    (seq_executes _ _ g hd (weightRestore_executes g _)))),?_⟩
  have hi : i.val ≤ d := by omega
  have hk : k ≤ d := Nat.sub_le _ _
  have hta := hba.trans (factorialTime_mono hi)
  have htb := hbb.trans (factorialTime_mono hk)
  let L := (d+1)^2+2
  have hA : (Computability.encodeNat i.val.factorial).length ≤ L :=
    (factorial_binary_length i.val).trans (by dsimp [L]; nlinarith)
  have hB : (Computability.encodeNat k.factorial).length ≤ L :=
    (factorial_binary_length k).trans (by dsimp [L]; nlinarith)
  have hS : (signedBits (interpolationDenominator d i)).length ≤ L := by
    have hh := (interpolation_weights_bit_bound d i).1
    simp only [signedBits,List.length_cons,encodeNat_length]
    dsimp [L]; nlinarith
  have htc' : tc ≤ 18+2*L+L*(5*(L*(L+2))+10*L+22)+d+L :=
    hbc.trans (by gcongr)
  simp only [denominatorUnaryTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_ofNat,Polynomial.eval_one,Polynomial.eval_X]
  change _ ≤ 2*factorialTime.eval d+L*(5*(L*(L+2))+10*L+22)+10*L+6*d+40
  omega

lemma denominatorUnary_queryFree : denominatorUnary.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (rename_queryFree _ _ factorialBlock_queryFree)
      (seq_queryFree _ _ (rename_queryFree _ _ factorialBlock_queryFree)
        (seq_queryFree _ _ (rename_queryFree _ _ denominatorCombine_queryFree)
          (seq_queryFree _ _ (reverseOn_queryFree _ _ _) (reverseOn_queryFree _ _ _)))))

end HiddenCircuits.Complexity.BinaryArithmetic
