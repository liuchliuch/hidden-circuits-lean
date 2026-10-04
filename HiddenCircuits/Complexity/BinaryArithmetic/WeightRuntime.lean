import HiddenCircuits.Complexity.BinaryArithmetic.NumeratorUnary

/-! Clean finite-machine generation of both consecutive interpolation weights. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic
open OracleBlock OracleMachine

 theorem denominatorUnary_runs (g : BitString → ℕ) (d : ℕ) (i : Fin (d+1)) :
    ∃ (c : denominatorUnary.machine.Config) (t : ℕ),
      denominatorUnary.machine.Runs g
        (denominatorUnary.config denominatorUnary.start
          (weightStore (List.replicate i.val true) (List.replicate (d-i.val) true) [] [] [] [])) c t ∧
      c.stack = weightStore (signedBits (interpolationDenominator d i)) [] [] [] [] [] ∧
      t ≤ denominatorUnaryTime.eval d := by
  obtain ⟨t,ht,hbound⟩ := denominatorUnary_executes g d i
  refine ⟨denominatorUnary.config denominatorUnary.exit
    (weightStore (signedBits (interpolationDenominator d i)) [] [] [] [] []),t,?_,rfl,hbound⟩
  apply (runs_iff_steps_halt _).mpr
  exact ⟨ht,by simp [OracleMachine.step,machine,config,denominatorUnary.exit_halt]⟩

 theorem numeratorUnary_runs (g : BitString → ℕ) (d : ℕ) (i : Fin (d+1)) :
    ∃ (c : numeratorUnary.machine.Config) (t : ℕ),
      numeratorUnary.machine.Runs g
        (numeratorUnary.config numeratorUnary.start
          (weightStore (List.replicate i.val true) (List.replicate (d-i.val) true) [] [] [] [])) c t ∧
      c.stack = weightStore (signedBits (interpolationNegativeNumerator d i)) [] [] [] [] [] ∧
      t ≤ numeratorUnaryTime.eval d := by
  obtain ⟨t,ht,hbound⟩ := numeratorUnary_executes g d i
  refine ⟨numeratorUnary.config numeratorUnary.exit
    (weightStore (signedBits (interpolationNegativeNumerator d i)) [] [] [] [] []),t,?_,rfl,hbound⟩
  apply (runs_iff_steps_halt _).mpr
  exact ⟨ht,by simp [OracleMachine.step,machine,config,numeratorUnary.exit_halt]⟩

def weightPairStore (a b savedI savedK : BitString) : Store 11 := fun j =>
  if j.val=0 then a else if j.val=1 then b else if j.val=10 then savedI else if j.val=11 then savedK else []

def weightPairDenominatorEmbedding : Fin 10 ↪ Fin 12 where
  toFun i := i.castLE (by decide)
  inj' := by intro i j h; exact Fin.ext (congrArg (fun q : Fin 12 => q.val) h)

def weightPairNumeratorEmbedding : Fin 10 ↪ Fin 12 where
  toFun i := if i=0 then 10 else if i=1 then 11 else i.castLE (by decide)
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

noncomputable def weightPairDenominator : OracleBlock 11 := rename denominatorUnary weightPairDenominatorEmbedding
noncomputable def weightPairNumerator : OracleBlock 11 := rename numeratorUnary weightPairNumeratorEmbedding
noncomputable def weightPairRestore : OracleBlock 11 :=
  seq (reverseOn 10 2 (by decide)) (reverseOn 2 1 (by decide))

 theorem weightPairRestore_executes (g : BitString → ℕ) (a num : BitString) :
    weightPairRestore.Executes g (weightPairStore a [] num []) (weightPairStore a num [] [])
      (4*num.length+4) := by
  let middle : Store 11 := fun j => if j.val=0 then a else if j.val=2 then num.reverse else []
  have h1 : (reverseOn (10 : Fin 12) 2 (by decide)).Executes g
      (weightPairStore a [] num []) middle (2*num.length+1) := by
    convert reverseOn_executes g (10 : Fin 12) 2 (by decide) (weightPairStore a [] num []) using 1
    funext j; fin_cases j <;> simp [weightPairStore,middle]
  have h2 : (reverseOn (2 : Fin 12) 1 (by decide)).Executes g
      middle (weightPairStore a num [] []) (2*num.length+1) := by
    convert reverseOn_executes g (2 : Fin 12) 1 (by decide) middle using 1
    · funext j; fin_cases j <;> simp [weightPairStore,middle]
    · simp [middle]
  convert seq_executes _ _ g h1 h2 using 1 <;> omega

/-- Save the two actual unary inputs, generate the denominator, then reuse the
same work stacks for the numerator while preserving the completed denominator. -/
noncomputable def weightPairUnary : OracleBlock 11 :=
  seq (copyOn 0 10 2 (by decide) (by decide) (by decide))
    (seq (copyOn 1 11 2 (by decide) (by decide) (by decide))
      (seq weightPairDenominator (seq weightPairNumerator weightPairRestore)))

noncomputable def weightPairUnaryTime : Polynomial ℕ :=
  denominatorUnaryTime+numeratorUnaryTime+5*Polynomial.X+4*((Polynomial.X+1)^2+2)+16

 theorem weightPairUnary_executes (g : BitString → ℕ) (d : ℕ) (i : Fin (d+1)) :
    ∃ t, weightPairUnary.Executes g
      (weightPairStore (List.replicate i.val true) (List.replicate (d-i.val) true) [] [])
      (weightPairStore (signedBits (interpolationDenominator d i))
        (signedBits (interpolationNegativeNumerator d i)) [] []) t ∧
      t ≤ weightPairUnaryTime.eval d := by
  have h1 : (copyOn (0 : Fin 12) 10 2 (by decide) (by decide) (by decide)).Executes g
      (weightPairStore (List.replicate i.val true) (List.replicate (d-i.val) true) [] [])
      (weightPairStore (List.replicate i.val true) (List.replicate (d-i.val) true) (List.replicate i.val true) [])
      (5*i.val+2) := by
    convert copyOn_executes g (0 : Fin 12) 10 2 (by decide) (by decide) (by decide)
      (weightPairStore (List.replicate i.val true) (List.replicate (d-i.val) true) [] []) rfl using 1
    · funext j; fin_cases j <;> simp [weightPairStore]
    · simp [weightPairStore]
  have h2 : (copyOn (1 : Fin 12) 11 2 (by decide) (by decide) (by decide)).Executes g
      (weightPairStore (List.replicate i.val true) (List.replicate (d-i.val) true) (List.replicate i.val true) [])
      (weightPairStore (List.replicate i.val true) (List.replicate (d-i.val) true)
        (List.replicate i.val true) (List.replicate (d-i.val) true)) (5*(d-i.val)+2) := by
    convert copyOn_executes g (1 : Fin 12) 11 2 (by decide) (by decide) (by decide)
      (weightPairStore (List.replicate i.val true) (List.replicate (d-i.val) true) (List.replicate i.val true) []) rfl using 1
    · funext j; fin_cases j <;> simp [weightPairStore]
    · simp [weightPairStore]
  obtain ⟨td,hd,hbd⟩ := denominatorUnary_executes g d i
  have h3 : weightPairDenominator.Executes g
      (weightPairStore (List.replicate i.val true) (List.replicate (d-i.val) true)
        (List.replicate i.val true) (List.replicate (d-i.val) true))
      (weightPairStore (signedBits (interpolationDenominator d i)) []
        (List.replicate i.val true) (List.replicate (d-i.val) true)) td := by
    apply rename_executes_to denominatorUnary weightPairDenominatorEmbedding g hd
    · funext j; fin_cases j <;> rfl
    · funext j; fin_cases j <;> rfl
    · intro j hj; fin_cases j <;> first | rfl | (exfalso; exact hj 0 rfl) | (exfalso; exact hj 1 rfl)
  obtain ⟨tn,hn,hbn⟩ := numeratorUnary_executes g d i
  have h4 : weightPairNumerator.Executes g
      (weightPairStore (signedBits (interpolationDenominator d i)) []
        (List.replicate i.val true) (List.replicate (d-i.val) true))
      (weightPairStore (signedBits (interpolationDenominator d i)) []
        (signedBits (interpolationNegativeNumerator d i)) []) tn := by
    apply rename_executes_to numeratorUnary weightPairNumeratorEmbedding g hn
    · funext j; fin_cases j <;> rfl
    · funext j; fin_cases j <;> rfl
    · intro j hj; fin_cases j <;> first | rfl | (exfalso; exact hj 0 rfl) | (exfalso; exact hj 1 rfl)
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2
    (seq_executes _ _ g h3 (seq_executes _ _ g h4 (weightPairRestore_executes g _ _)))),?_⟩
  have hS : (signedBits (interpolationNegativeNumerator d i)).length ≤ (d+1)^2+2 := by
    have hh := (interpolation_weights_bit_bound d i).2
    simp only [signedBits,List.length_cons,encodeNat_length]
    have hp : d^2 ≤ (d+1)^2 := Nat.pow_le_pow_left (show d ≤ d+1 from Nat.le_succ d) 2
    omega
  have he : i.val+(d-i.val)=d := Nat.add_sub_of_le (by omega)
  simp only [weightPairUnaryTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_ofNat,Polynomial.eval_one,Polynomial.eval_X]
  omega

lemma weightPairUnary_queryFree : weightPairUnary.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
      (seq_queryFree _ _ (rename_queryFree _ _ denominatorUnary_queryFree)
        (seq_queryFree _ _ (rename_queryFree _ _ numeratorUnary_queryFree)
          (seq_queryFree _ _ (reverseOn_queryFree _ _ _) (reverseOn_queryFree _ _ _)))))

 theorem weightPairUnary_runs (g : BitString → ℕ) (d : ℕ) (i : Fin (d+1)) :
    ∃ (c : weightPairUnary.machine.Config) (t : ℕ),
      weightPairUnary.machine.Runs g
        (weightPairUnary.config weightPairUnary.start
          (weightPairStore (List.replicate i.val true) (List.replicate (d-i.val) true) [] [])) c t ∧
      c.stack = weightPairStore (signedBits (interpolationDenominator d i))
        (signedBits (interpolationNegativeNumerator d i)) [] [] ∧
      t ≤ weightPairUnaryTime.eval d := by
  obtain ⟨t,ht,hbound⟩ := weightPairUnary_executes g d i
  refine ⟨weightPairUnary.config weightPairUnary.exit
    (weightPairStore (signedBits (interpolationDenominator d i))
      (signedBits (interpolationNegativeNumerator d i)) [] []),t,?_,rfl,hbound⟩
  apply (runs_iff_steps_halt _).mpr
  exact ⟨ht,by simp [OracleMachine.step,machine,config,weightPairUnary.exit_halt]⟩

end HiddenCircuits.Complexity.BinaryArithmetic
