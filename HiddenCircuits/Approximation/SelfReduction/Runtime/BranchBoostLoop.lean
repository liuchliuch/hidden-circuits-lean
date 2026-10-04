import HiddenCircuits.Approximation.SelfReduction.Runtime.BranchBoostBody

/-! A finite scan of every padded partner computes the exact vector of boosted
frequencies. The same sample matrix is preserved across all candidates. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

noncomputable def branchBoostLoop : OracleBlock 20 := whilePop 19 branchBoostBody branchBoostBody

def branchValues (n radius : ℕ) (groups : Fin (n+1) → List BitString) : ℕ → ℕ → List ℕ
  | _,0 => []
  | idx,count+1 => branchBoostValue n radius groups idx :: branchValues n radius groups (idx+1) count

 theorem branchValues_ofFn (n radius : ℕ) (groups : Fin (n+1) → List BitString) (idx count : ℕ) :
    branchValues n radius groups idx count=List.ofFn (fun i : Fin count => branchBoostValue n radius groups (idx+i.val)) := by
  induction count generalizing idx with
  | zero => simp [branchValues]
  | succ count ih =>
    rw [branchValues,List.ofFn_succ,ih]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ]
    congr 2
    funext i
    congr 1
    omega

noncomputable def branchIterationBound (n M B radius cap dataLength : ℕ) : ℕ :=
  5*dataLength+(n+1)*(110*(M+1)*(B+cap+2))+12*(n+1)*(M+1)+5*radius+
    2000*(n+2)^2*(M+radius+1)+9*M+235

 theorem branchBoostLoop_execution (g : BitString → ℕ) (n M B radius cap : ℕ)
    (groups : Fin (n+1) → List BitString) (hM : ∀ i, (groups i).length ≤ M)
    (hB : ∀ i, ∀ x ∈ groups i, x.length ≤ B) (count idx : ℕ) (hcap : idx+count ≤ cap) (out : BitString) :
    ∃ t, WhileExecution (19 : Fin 21) branchBoostBody branchBoostBody g
      (branchStore idx radius count (groupWords (List.ofFn groups)) out 0)
      (branchStore (idx+count) radius 0 (groupWords (List.ofFn groups))
        ((unaryValues (branchValues n radius groups idx count)).reverse++out) 0) t ∧
      t ≤ 1+count*branchIterationBound n M B radius cap (groupWords (List.ofFn groups)).length := by
  induction count generalizing idx out with
  | zero =>
    refine ⟨1,?_,by simp⟩
    simpa [branchValues,unaryValues,encodeBitList] using
      (WhileExecution.empty (branchStore idx radius 0 (groupWords (List.ofFn groups)) out 0) (by rfl))
  | succ count ih =>
    obtain ⟨tb,hb,hbt⟩ := branchBoostBody_executes g n M B radius idx count groups hM hB out
    obtain ⟨tt,ht,htt⟩ := ih (idx+1) (by omega)
      ((true::pairBits (List.replicate (branchBoostValue n radius groups idx) true) []).reverse++out)
    have hpop : Function.update (branchStore idx radius (count+1) (groupWords (List.ofFn groups)) out 0)
        (19 : Fin 21) (List.replicate count true) =
        branchStore idx radius count (groupWords (List.ofFn groups)) out 0 := by
      funext i; fin_cases i <;> rfl
    have hw := WhileExecution.one
      (s := branchStore idx radius (count+1) (groupWords (List.ofFn groups)) out 0)
      (rest := List.replicate count true) (by rfl) (by rw [hpop]; exact hb) ht
    refine ⟨2+tb+tt,?_,?_⟩
    · convert hw using 1
      · simp only [branchValues,unaryValues_reverse_cons,List.append_assoc]
        congr 1 <;> omega
      · omega
    · have hbody : tb+2 ≤ branchIterationBound n M B radius cap (groupWords (List.ofFn groups)).length := by
        apply hbt.trans
        unfold branchIterationBound
        gcongr
        omega
      nlinarith

 theorem branchBoostLoop_executes (g : BitString → ℕ) (n M B radius cap : ℕ)
    (groups : Fin (n+1) → List BitString) (hM : ∀ i, (groups i).length ≤ M)
    (hB : ∀ i, ∀ x ∈ groups i, x.length ≤ B) :
    ∃ t, branchBoostLoop.Executes g (branchStore 0 radius cap (groupWords (List.ofFn groups)) [] 0)
      (branchStore cap radius 0 (groupWords (List.ofFn groups))
        (unaryValues (List.ofFn (fun i : Fin cap => branchBoostValue n radius groups i.val))).reverse 0) t ∧
      t ≤ 1+cap*branchIterationBound n M B radius cap (groupWords (List.ofFn groups)).length := by
  obtain ⟨t,ht,hb⟩ := branchBoostLoop_execution g n M B radius cap groups hM hB cap 0 (by omega) []
  refine ⟨t,?_,hb⟩
  simpa only [branchValues_ofFn,Nat.zero_add,List.append_nil] using whilePop_executes _ _ _ _ ht

end HiddenCircuits.Approximation.SelfReduction.Runtime
