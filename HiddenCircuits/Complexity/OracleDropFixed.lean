import HiddenCircuits.Complexity.OracleCleanup

/-! Fixed-count saturating pops, implemented as finite control rather than
unit-cost unary subtraction. -/
namespace HiddenCircuits.Complexity.OracleBlock
variable {k : ℕ}

noncomputable def dropFixed (stack : Fin (k+1)) : ℕ → OracleBlock k
  | 0 => skip
  | n+1 => branchPop stack skip (dropFixed stack n) (dropFixed stack n)

theorem dropFixed_executes (g : BitString → ℕ) (stack : Fin (k+1)) (n : ℕ) (s : Store k) :
    ∃ cost, (dropFixed stack n).Executes g s (Function.update s stack ((s stack).drop n)) cost ∧
      cost ≤ 2*n+3 := by
  induction n generalizing s with
  | zero => exact ⟨1,by simpa [dropFixed] using skip_executes g s,by omega⟩
  | succ n ih =>
    cases hs : s stack with
    | nil =>
      refine ⟨3,?_,by omega⟩
      have h := branchPop_empty stack skip (dropFixed stack n) (dropFixed stack n) g hs (skip_executes g s)
      have he : Function.update s stack [] = s := by rw [← hs];simp
      simpa only [hs,List.drop_nil,he] using h
    | cons bit xs =>
      let s' := Function.update s stack xs
      obtain ⟨cost,hc,hb⟩ := ih s'
      refine ⟨cost+2,?_,by omega⟩
      have h : (dropFixed stack (n+1)).Executes g s (Function.update s' stack ((s' stack).drop n)) (cost+2) := by
        cases bit
        · exact branchPop_false stack skip _ _ g hs hc
        · exact branchPop_true stack skip _ _ g hs hc
      simpa [s',hs] using h

lemma dropFixed_queryFree (stack : Fin (k+1)) (n : ℕ) : (dropFixed stack n).QueryFree := by
  induction n with
  | zero => exact skip_queryFree
  | succ n ih => exact branchPop_queryFree _ _ _ _ skip_queryFree ih ih

end HiddenCircuits.Complexity.OracleBlock
