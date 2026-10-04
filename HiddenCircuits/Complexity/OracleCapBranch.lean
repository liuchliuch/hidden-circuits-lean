import HiddenCircuits.Complexity.OracleCleanup

/-! Finite branching on a capped stack length. At most a fixed number of bits are
inspected and restored before executing the selected actual branch program. -/
namespace HiddenCircuits.Complexity.OracleBlock
variable {k : ℕ}

noncomputable def branchLength (stack : Fin (k+1)) : (cap : ℕ) → (Fin (cap+1) → OracleBlock k) → OracleBlock k
  | 0, branches => branches 0
  | cap+1, branches => branchPop stack (branches 0)
      (branchLength stack cap (fun i => seq (push stack false) (branches i.succ)))
      (branchLength stack cap (fun i => seq (push stack true) (branches i.succ)))

def cappedLength (cap : ℕ) (s : BitString) : Fin (cap+1) := ⟨min cap s.length,by omega⟩

/-- The branch receives the original store, including the completely restored
inspected stack. The overhead is bounded solely by the fixed program cap. -/
theorem branchLength_executes (g : BitString → ℕ) (stack : Fin (k+1)) (cap : ℕ)
    (branches : Fin (cap+1) → OracleBlock k) (s t : Store k) (cost : ℕ)
    (h : (branches (cappedLength cap (s stack))).Executes g s t cost) :
    ∃ overhead, (branchLength stack cap branches).Executes g s t (cost+overhead) ∧ overhead ≤ 5*cap+2 := by
  induction cap generalizing s cost with
  | zero => exact ⟨0,by simpa [branchLength,cappedLength] using h,by omega⟩
  | succ cap ih =>
    cases hs : s stack with
    | nil =>
      refine ⟨2,?_,by omega⟩
      apply branchPop_empty stack (branches 0) _ _ g hs
      simpa [cappedLength,hs] using h
    | cons bit xs =>
      let s' := Function.update s stack xs
      let branches' := fun i : Fin (cap+1) => seq (push stack bit) (branches i.succ)
      have hid : (cappedLength cap (s' stack)).succ = cappedLength (cap+1) (s stack) := by
        apply Fin.ext
        simp [cappedLength,s',hs]
      have hrestore : Function.update s' stack (bit::s' stack) = s := by
        simp [s',← hs]
      have hbody : (branches' (cappedLength cap (s' stack))).Executes g s' t (cost+3) := by
        have hp := push_executes g stack bit s'
        rw [hrestore] at hp
        have hr := seq_executes _ _ g hp (hid ▸ h)
        convert hr using 1 <;> omega
      obtain ⟨overhead,hr,hbound⟩ := ih branches' s' (cost+3) hbody
      refine ⟨overhead+5,?_,by omega⟩
      have hout : (branchLength stack (cap+1) branches).Executes g s t (cost+3+overhead+2) := by
        cases bit
        · exact branchPop_false stack _ _ _ g hs hr
        · exact branchPop_true stack _ _ _ g hs hr
      convert hout using 1 <;> omega

lemma branchLength_queryFree (stack : Fin (k+1)) (cap : ℕ) (branches : Fin (cap+1) → OracleBlock k)
    (hq : ∀ i, (branches i).QueryFree) : (branchLength stack cap branches).QueryFree := by
  induction cap with
  | zero => exact hq 0
  | succ cap ih =>
    apply branchPop_queryFree _ _ _ _ (hq 0)
    · exact ih _ (fun i => seq_queryFree _ _ (push_queryFree _ _) (hq i.succ))
    · exact ih _ (fun i => seq_queryFree _ _ (push_queryFree _ _) (hq i.succ))

end HiddenCircuits.Complexity.OracleBlock
