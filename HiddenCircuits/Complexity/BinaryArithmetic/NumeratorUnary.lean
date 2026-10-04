import HiddenCircuits.Complexity.BinaryArithmetic.DenominatorUnary
import HiddenCircuits.Complexity.BinaryArithmetic.UnaryBinary

/-! Exact negative-evaluation numerators from consecutive unary node indices. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic
open OracleBlock OracleMachine

noncomputable def numeratorSetup : OracleBlock 9 :=
  seq (copyOn 0 8 2 (by decide) (by decide) (by decide))
    (seq (reverseOn 1 0 (by decide))
      (seq (copyOn 0 9 2 (by decide) (by decide) (by decide))
        (seq (push 0 true) (push 8 true))))

 theorem numeratorSetup_executes (g : BitString → ℕ) (i k : ℕ) :
    numeratorSetup.Executes g
      (weightStore (List.replicate i true) (List.replicate k true) [] [] [] [])
      (weightStore (List.replicate (i+k+1) true) [] [] []
        (List.replicate (i+1) true) (List.replicate (i+k) true)) (5*i+2*k+5*(i+k)+15) := by
  have h1 : (copyOn (0 : Fin 10) 8 2 (by decide) (by decide) (by decide)).Executes g
      (weightStore (List.replicate i true) (List.replicate k true) [] [] [] [])
      (weightStore (List.replicate i true) (List.replicate k true) [] [] (List.replicate i true) []) (5*i+2) := by
    convert copyOn_executes g (0 : Fin 10) 8 2 (by decide) (by decide) (by decide)
      (weightStore (List.replicate i true) (List.replicate k true) [] [] [] []) rfl using 1
    · funext j; fin_cases j <;> simp [weightStore]
    · simp [weightStore]
  have h2 : (reverseOn (1 : Fin 10) 0 (by decide)).Executes g
      (weightStore (List.replicate i true) (List.replicate k true) [] [] (List.replicate i true) [])
      (weightStore (List.replicate (i+k) true) [] [] [] (List.replicate i true) []) (2*k+1) := by
    convert reverseOn_executes g (1 : Fin 10) 0 (by decide)
      (weightStore (List.replicate i true) (List.replicate k true) [] [] (List.replicate i true) []) using 1
    · funext j; fin_cases j <;> simp [weightStore,← List.replicate_add,Nat.add_comm]
    · simp [weightStore]
  have h3 : (copyOn (0 : Fin 10) 9 2 (by decide) (by decide) (by decide)).Executes g
      (weightStore (List.replicate (i+k) true) [] [] [] (List.replicate i true) [])
      (weightStore (List.replicate (i+k) true) [] [] [] (List.replicate i true) (List.replicate (i+k) true))
      (5*(i+k)+2) := by
    convert copyOn_executes g (0 : Fin 10) 9 2 (by decide) (by decide) (by decide)
      (weightStore (List.replicate (i+k) true) [] [] [] (List.replicate i true) []) rfl using 1
    · funext j; fin_cases j <;> simp [weightStore]
    · simp [weightStore]
  have h4 : (push (0 : Fin 10) true).Executes g
      (weightStore (List.replicate (i+k) true) [] [] [] (List.replicate i true) (List.replicate (i+k) true))
      (weightStore (List.replicate (i+k+1) true) [] [] [] (List.replicate i true) (List.replicate (i+k) true)) 1 := by
    convert push_executes g (0 : Fin 10) true
      (weightStore (List.replicate (i+k) true) [] [] [] (List.replicate i true) (List.replicate (i+k) true)) using 1
    funext j; fin_cases j <;> simp [weightStore,List.replicate_succ]
  have h5 : (push (8 : Fin 10) true).Executes g
      (weightStore (List.replicate (i+k+1) true) [] [] [] (List.replicate i true) (List.replicate (i+k) true))
      (weightStore (List.replicate (i+k+1) true) [] [] [] (List.replicate (i+1) true) (List.replicate (i+k) true)) 1 := by
    convert push_executes g (8 : Fin 10) true
      (weightStore (List.replicate (i+k+1) true) [] [] [] (List.replicate i true) (List.replicate (i+k) true)) using 1
    funext j; fin_cases j <;> simp [weightStore,List.replicate_succ]
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 (seq_executes _ _ g h4 h5))) using 1 <;> omega

def weightCounterEmbedding : Fin 3 ↪ Fin 10 where
  toFun i := if i=0 then 8 else if i=1 then 1 else 2
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

noncomputable def weightCounter : OracleBlock 9 := rename unaryBinary weightCounterEmbedding

 theorem weightCounter_executes (g : BitString → ℕ) (a clock : BitString) (n : ℕ) :
    weightCounter.Executes g (weightStore a [] [] [] (List.replicate n true) clock)
      (weightStore a (Computability.encodeNat n) [] [] [] clock) (unaryBinaryCost 0 n) := by
  have h := unaryBinary_executes g (List.replicate n true) 0
  simp only [List.length_replicate,Nat.zero_add] at h
  apply rename_executes_to unaryBinary weightCounterEmbedding g h
  · funext j; fin_cases j <;> rfl
  · funext j; fin_cases j <;> rfl
  · intro j hj; fin_cases j <;> first | rfl | (exfalso; exact hj 0 rfl) | (exfalso; exact hj 1 rfl)

noncomputable def numeratorRestore : OracleBlock 9 :=
  seq (reverseOn 3 2 (by decide)) (reverseOn 2 0 (by decide))

 theorem numeratorRestore_executes (g : BitString → ℕ) (xs : BitString) :
    numeratorRestore.Executes g (weightStore [] [] [] xs [] [])
      (weightStore xs [] [] [] [] []) (4*xs.length+4) := by
  have h1 : (reverseOn (3 : Fin 10) 2 (by decide)).Executes g
      (weightStore [] [] [] xs [] []) (weightStore [] [] xs.reverse [] [] []) (2*xs.length+1) := by
    convert reverseOn_executes g (3 : Fin 10) 2 (by decide) (weightStore [] [] [] xs [] []) using 1
    funext i; fin_cases i <;> simp [weightStore]
  have h2 : (reverseOn (2 : Fin 10) 0 (by decide)).Executes g
      (weightStore [] [] xs.reverse [] [] []) (weightStore xs [] [] [] [] []) (2*xs.length+1) := by
    convert reverseOn_executes g (2 : Fin 10) 0 (by decide) (weightStore [] [] xs.reverse [] [] []) using 1
    · funext i; fin_cases i <;> simp [weightStore]
    · simp [weightStore]
  convert seq_executes _ _ g h1 h2 using 1 <;> omega

noncomputable def numeratorUnary : OracleBlock 9 :=
  seq numeratorSetup (seq (weightFactor 0) (seq weightCounter (seq numeratorCombine numeratorRestore)))

noncomputable def numeratorUnaryTime : Polynomial ℕ :=
  let L : Polynomial ℕ := (Polynomial.X+1)^2+2
  factorialTime.comp (Polynomial.X+1)+L*(25*L+54)+
    (Polynomial.X+1)*(4*(Polynomial.X+1)+5)+5*L+16*Polynomial.X+60

 theorem numeratorUnary_executes (g : BitString → ℕ) (d : ℕ) (i : Fin (d+1)) :
    ∃ t, numeratorUnary.Executes g
      (weightStore (List.replicate i.val true) (List.replicate (d-i.val) true) [] [] [] [])
      (weightStore (signedBits (interpolationNegativeNumerator d i)) [] [] [] [] []) t ∧
      t ≤ numeratorUnaryTime.eval d := by
  have he : i.val+(d-i.val)=d := Nat.add_sub_of_le (by omega)
  have hs := numeratorSetup_executes g i.val (d-i.val)
  rw [he] at hs
  obtain ⟨ta,ha,hba⟩ := weightFactor_left g (List.replicate (d+1) true) []
    (List.replicate (i.val+1) true) (List.replicate d true)
  simp only [List.length_replicate] at ha hba
  have hc := weightCounter_executes g (Computability.encodeNat (d+1).factorial) (List.replicate d true) (i.val+1)
  obtain ⟨tc,hcc,hbc⟩ := numeratorCombine_executes g d i
  have hd : numeratorCombine.Executes g
      (weightStore (Computability.encodeNat (d+1).factorial) (Computability.encodeNat (i.val+1)) [] [] [] (List.replicate d true))
      (weightStore [] [] [] (signedBits (interpolationNegativeNumerator d i)) [] []) tc := by
    convert hcc using 1 <;> funext j <;> fin_cases j <;> rfl
  refine ⟨_,seq_executes _ _ g hs (seq_executes _ _ g ha
    (seq_executes _ _ g hc (seq_executes _ _ g hd (numeratorRestore_executes g _)))),?_⟩
  let L := (d+1)^2+2
  have hA : (Computability.encodeNat (d+1).factorial).length ≤ L :=
    (factorial_binary_length (d+1)).trans (by dsimp [L]; nlinarith)
  have hB : (Computability.encodeNat (i.val+1)).length ≤ L := by
    rw [encodeNat_length]
    refine (Nat.size_le.mpr (Nat.lt_two_pow_self (n := i.val+1))).trans ?_
    dsimp [L]; nlinarith [i.isLt]
  have hS : (signedBits (interpolationNegativeNumerator d i)).length ≤ L := by
    have hh := (interpolation_weights_bit_bound d i).2
    simp only [signedBits,List.length_cons,encodeNat_length]
    dsimp [L]; nlinarith
  have htc : tc ≤ L*(25*L+54)+d+L+18 := hbc.trans (by gcongr)
  have hcounter := unaryBinaryCost_le (i.val+1) 0 (d+1) (by omega)
  have hcounter' : unaryBinaryCost 0 (i.val+1) ≤ 1+(d+1)*(4*(d+1)+5) :=
    hcounter.trans (by gcongr; omega)
  simp only [numeratorUnaryTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_ofNat,Polynomial.eval_one,Polynomial.eval_X,Polynomial.eval_comp]
  change _ ≤ factorialTime.eval (d+1)+L*(25*L+54)+(d+1)*(4*(d+1)+5)+5*L+16*d+60
  omega

lemma numeratorUnary_queryFree : numeratorUnary.QueryFree := by
  have hs : numeratorSetup.QueryFree :=
    seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
      (seq_queryFree _ _ (reverseOn_queryFree _ _ _)
        (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
          (seq_queryFree _ _ (push_queryFree _ _) (push_queryFree _ _))))
  exact seq_queryFree _ _ hs (seq_queryFree _ _ (rename_queryFree _ _ factorialBlock_queryFree)
    (seq_queryFree _ _ (rename_queryFree _ _ unaryBinary_queryFree)
      (seq_queryFree _ _ numeratorCombine_queryFree
        (seq_queryFree _ _ (reverseOn_queryFree _ _ _) (reverseOn_queryFree _ _ _)))))

end HiddenCircuits.Complexity.BinaryArithmetic
