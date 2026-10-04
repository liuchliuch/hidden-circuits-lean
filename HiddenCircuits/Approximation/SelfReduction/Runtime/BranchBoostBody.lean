import HiddenCircuits.Approximation.SelfReduction.Runtime.GroupBoost

/-! One actual branch-statistics iteration. All confidence groups are reused for
all candidate partners, exactly as in the finite probability analysis. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

def branchStore (idx radius remaining : ℕ) (groups out : BitString) (value : ℕ) : Store 20 := fun i =>
  if i.val=0 then List.replicate (idx+1) true else if i.val=1 then List.replicate value true
  else if i.val=17 then List.replicate radius true else if i.val=18 then groups
  else if i.val=19 then List.replicate remaining true else if i.val=20 then out else []

def branchBoostPorts : Fin 18 ↪ Fin 21 where
  toFun i := i.castAdd 3
  inj' := by intro i j h; exact Fin.ext (congrArg (fun x : Fin 21 => x.val) h)

noncomputable def branchBoostBody : OracleBlock 20 :=
  seq (copyOn 18 10 3 (by decide) (by decide) (by decide))
    (seq (rename groupBoost branchBoostPorts) (seq (emitUnaryReversed 1 20) (push 0 true)))

def branchBoostValue (n radius : ℕ) (groups : Fin (n+1) → List BitString) (idx : ℕ) : ℕ :=
  groupBoostValue n radius (List.replicate (idx+1) true) groups

 theorem branchBoostValue_le (n radius M : ℕ) (groups : Fin (n+1) → List BitString)
    (hM : ∀ i, (groups i).length ≤ M) (idx : ℕ) : branchBoostValue n radius groups idx ≤ M :=
  List.countP_le_length.trans (hM _)

 theorem branchBoostBody_executes (g : BitString → ℕ) (n M B radius idx remaining : ℕ)
    (groups : Fin (n+1) → List BitString) (hM : ∀ i, (groups i).length ≤ M)
    (hB : ∀ i, ∀ x ∈ groups i, x.length ≤ B) (out : BitString) :
    ∃ t, branchBoostBody.Executes g (branchStore idx radius remaining (groupWords (List.ofFn groups)) out 0)
      (branchStore (idx+1) radius remaining (groupWords (List.ofFn groups))
        ((true::pairBits (List.replicate (branchBoostValue n radius groups idx) true) []).reverse++out) 0) t ∧
      t+2 ≤ 5*(groupWords (List.ofFn groups)).length+
        (n+1)*(110*(M+1)*(B+idx+2))+12*(n+1)*(M+1)+5*radius+
        2000*(n+2)^2*(M+radius+1)+9*M+235 := by
  let data := groupWords (List.ofFn groups)
  let c := branchBoostValue n radius groups idx
  let s1 := Function.update (branchStore idx radius remaining data out 0) (10 : Fin 21) data
  have h1 : (copyOn (18 : Fin 21) 10 3 (by decide) (by decide) (by decide)).Executes g
      (branchStore idx radius remaining data out 0) s1 (5*data.length+2) := by
    convert copyOn_executes g (18 : Fin 21) 10 3 (by decide) (by decide) (by decide)
      (branchStore idx radius remaining data out 0) rfl using 1
    funext i; fin_cases i <;> simp [s1,branchStore]
  obtain ⟨tb,hb,hbb⟩ := groupBoost_executes g n M B radius (List.replicate (idx+1) true) groups hM hB
  have h2 : (rename groupBoost branchBoostPorts).Executes g s1
      (branchStore idx radius remaining data out c) tb := by
    apply rename_executes_to groupBoost branchBoostPorts g hb
    · funext i; fin_cases i <;> simp [s1,branchStore,boostStore,branchBoostPorts,data]
    · funext i; fin_cases i <;> simp [branchStore,boostStore,branchBoostPorts,c,branchBoostValue]
    · intro j hj; fin_cases j
      all_goals first | rfl | exact False.elim (hj 1 rfl) | exact False.elim (hj 10 rfl)
  let s2 := branchStore idx radius remaining data
    ((true::pairBits (List.replicate c true) []).reverse++out) 0
  have h3 : (emitUnaryReversed (1 : Fin 21) 20).Executes g (branchStore idx radius remaining data out c) s2
      (9*c+7) := by
    convert emitUnaryReversed_executes g (1 : Fin 21) 20 (by decide) (branchStore idx radius remaining data out c) using 1
    · funext i; fin_cases i <;> simp [s2,branchStore]
    · simp [branchStore]
  have h4 : (push (0 : Fin 21) true).Executes g s2
      (branchStore (idx+1) radius remaining data ((true::pairBits (List.replicate c true) []).reverse++out) 0) 1 := by
    convert push_executes g (0 : Fin 21) true s2 using 1
    funext i; fin_cases i <;> simp [s2,branchStore,List.replicate_succ]
  have hc : c ≤ M := branchBoostValue_le n radius M groups hM idx
  simp only [List.length_replicate] at hbb
  rw [show B+(idx+1)+1=B+idx+2 by omega] at hbb
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)),?_⟩
  dsimp only [data]
  omega

end HiddenCircuits.Approximation.SelfReduction.Runtime
