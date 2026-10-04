import HiddenCircuits.Approximation.SelfReduction.Runtime.ReadUnaryLe

/-! A physical unary radius
test copies both operands into disposable work stacks, performs two consuming
comparisons, and restores a clean work area. All instruction costs are charged. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
set_option maxHeartbeats 800000

def radiusWork (target radius item : ℕ) (out : BitString) (sum operand : ℕ) : Store 7 := fun i =>
  if i.val=0 then List.replicate target true
  else if i.val=1 then List.replicate radius true
  else if i.val=2 then List.replicate item true
  else if i.val=3 then out
  else if i.val=4 then List.replicate sum true
  else if i.val=5 then List.replicate operand true else []

def radiusStore (target radius item : ℕ) (out : BitString) : Store 7 :=
  radiusWork target radius item out 0 0

def radiusBasePort (swap : Bool) : Fin 8 := if swap then 2 else 0
def radiusOperandPort (swap : Bool) : Fin 8 := if swap then 0 else 2
def radiusBase (swap : Bool) (target item : ℕ) : ℕ := if swap then item else target
def radiusOperand (swap : Bool) (target item : ℕ) : ℕ := if swap then target else item

def radiusCompareEmbedding : Fin 3 ↪ Fin 8 where
  toFun i := if i.val=0 then 5 else if i.val=1 then 4 else 3
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

/-- Each half uses a disposable sum and operand rather than copying the sum
again for a read-only comparator. This keeps the fixed operational cost small. -/
noncomputable def radiusHalf (swap : Bool) : OracleBlock 7 :=
  seq (copyOn (radiusBasePort swap) 4 7
    (by cases swap <;> decide) (by cases swap <;> decide) (by decide))
    (seq (copyOn 1 4 7 (by decide) (by decide) (by decide))
      (seq (copyOn (radiusOperandPort swap) 5 7
        (by cases swap <;> decide) (by cases swap <;> decide) (by decide))
        (rename unaryLe radiusCompareEmbedding)))

theorem radiusHalf_executes (g : BitString → ℕ) (target radius item : ℕ)
    (out : BitString) (swap : Bool) :
    ∃ t, (radiusHalf swap).Executes g (radiusStore target radius item out)
      (radiusStore target radius item
        (decide (radiusOperand swap target item ≤ radiusBase swap target item + radius)::out)) t ∧
      t ≤ 8*(target+radius+item)+21 := by
  let base := radiusBase swap target item
  let operand := radiusOperand swap target item
  have h1 : (copyOn (radiusBasePort swap) 4 7
      (by cases swap <;> decide) (by cases swap <;> decide) (by decide)).Executes g
      (radiusStore target radius item out) (radiusWork target radius item out base 0)
      (5*base+2) := by
    convert copyOn_executes g (radiusBasePort swap) 4 7
      (by cases swap <;> decide) (by cases swap <;> decide) (by decide)
      (radiusStore target radius item out) rfl using 1
    · funext i; cases swap <;> fin_cases i <;>
        simp [radiusStore,radiusWork,radiusBasePort,base,radiusBase]
    · cases swap <;> simp [radiusStore,radiusWork,radiusBasePort,base,radiusBase]
  have h2 : (copyOn (1 : Fin 8) 4 7 (by decide) (by decide) (by decide)).Executes g
      (radiusWork target radius item out base 0)
      (radiusWork target radius item out (base+radius) 0) (5*radius+2) := by
    convert copyOn_executes g (1 : Fin 8) 4 7 (by decide) (by decide) (by decide)
      (radiusWork target radius item out base 0) rfl using 1
    · funext i; fin_cases i <;> simp [radiusWork,Nat.add_comm]
    · simp [radiusWork]
  have h3 : (copyOn (radiusOperandPort swap) 5 7
      (by cases swap <;> decide) (by cases swap <;> decide) (by decide)).Executes g
      (radiusWork target radius item out (base+radius) 0)
      (radiusWork target radius item out (base+radius) operand) (5*operand+2) := by
    convert copyOn_executes g (radiusOperandPort swap) 5 7
      (by cases swap <;> decide) (by cases swap <;> decide) (by decide)
      (radiusWork target radius item out (base+radius) 0) rfl using 1
    · funext i; cases swap <;> fin_cases i <;>
        simp [radiusWork,radiusOperandPort,operand,radiusOperand]
    · cases swap <;> simp [radiusWork,radiusOperandPort,operand,radiusOperand]
  obtain ⟨t,ht,hb⟩ := unaryLe_executes g (List.replicate operand true)
    (List.replicate (base+radius) true) out
  simp only [List.length_replicate] at ht hb
  have h4 : (rename unaryLe radiusCompareEmbedding).Executes g
      (radiusWork target radius item out (base+radius) operand)
      (radiusStore target radius item (decide (operand ≤ base+radius)::out)) t := by
    apply rename_executes_to unaryLe radiusCompareEmbedding g ht
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
    · intro j hj; fin_cases j
      all_goals first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) |
        exact False.elim (hj 2 rfl)
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)),?_⟩
  cases swap <;> simp only [base,operand,radiusBase,radiusOperand,Bool.false_eq_true,
    ↓reduceIte] at * <;> omega

theorem radiusHalf_queryFree (swap : Bool) : (radiusHalf swap).QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
      (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
        (rename_queryFree _ _ unaryLe_queryFree)))

noncomputable def radiusTest : OracleBlock 7 :=
  seq (radiusHalf false) (branchPop 3 (push 3 false) (push 3 false) (radiusHalf true))

theorem radiusTest_executes (g : BitString → ℕ) (target radius item : ℕ) :
    ∃ t, radiusTest.Executes g (radiusStore target radius item [])
      (radiusStore target radius item [decide (item ≤ target+radius ∧ target ≤ item+radius)]) t ∧
      t ≤ 50*(target+radius+item+1) := by
  obtain ⟨t1,h1,hb1⟩ := radiusHalf_executes g target radius item [] false
  simp only [radiusBase,radiusOperand,Bool.false_eq_true,↓reduceIte] at h1
  by_cases h : item ≤ target+radius
  · obtain ⟨t2,h2,hb2⟩ := radiusHalf_executes g target radius item [] true
    simp only [radiusBase,radiusOperand,↓reduceIte] at h2
    have hbranch : (branchPop (3 : Fin 8) (push 3 false) (push 3 false) (radiusHalf true)).Executes g
        (radiusStore target radius item [true])
        (radiusStore target radius item [decide (target ≤ item+radius)]) (t2+2) := by
      apply branchPop_true _ _ _ _ g rfl
      convert h2 using 1
      funext i; fin_cases i <;> rfl
    simp only [h,decide_true] at h1
    refine ⟨t1+(t2+2)+2,?_,by omega⟩
    simpa only [radiusTest,h,true_and] using seq_executes _ _ g h1 hbranch
  · have hpush : (push (3 : Fin 8) false).Executes g (radiusStore target radius item [])
        (radiusStore target radius item [false]) 1 := by
      convert push_executes g (3 : Fin 8) false (radiusStore target radius item []) using 1
      funext i; fin_cases i <;> rfl
    have hbranch : (branchPop (3 : Fin 8) (push 3 false) (push 3 false) (radiusHalf true)).Executes g
        (radiusStore target radius item [false]) (radiusStore target radius item [false]) (1+2) := by
      apply branchPop_false _ _ _ _ g rfl
      convert hpush using 1
      funext i; fin_cases i <;> rfl
    simp only [h,decide_false] at h1
    refine ⟨t1+(1+2)+2,?_,by omega⟩
    simpa only [radiusTest,h,false_and,decide_false] using seq_executes _ _ g h1 hbranch

theorem radiusTest_queryFree : radiusTest.QueryFree :=
  seq_queryFree _ _ (radiusHalf_queryFree false)
    (branchPop_queryFree _ _ _ _ (push_queryFree _ _) (push_queryFree _ _) (radiusHalf_queryFree true))

end HiddenCircuits.Approximation.SelfReduction.Runtime
