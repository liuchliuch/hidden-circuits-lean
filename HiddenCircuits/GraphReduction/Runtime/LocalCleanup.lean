import HiddenCircuits.Complexity.OracleCleanup

/-! Clearing selected work registers without bounding untouched framed streams. -/
namespace HiddenCircuits.GraphReduction.Runtime
open Complexity Complexity.OracleBlock

theorem clearList_executes_local {k : ℕ} (g : BitString → ℕ) (is : List (Fin (k+1))) (s : Store k)
    (B : ℕ) (hs : ∀ j∈is, (s j).length≤B) :
    ∃ c, (clearList is).Executes g s (eraseStore is s) c ∧ c ≤ is.length*(B+3)+1 := by
  induction is generalizing s with
  | nil => exact ⟨1,by simpa [clearList,eraseStore] using skip_executes g s,by simp⟩
  | cons i is ih =>
    have ht : ∀ j∈is, (Function.update s i [] j).length≤B := by
      intro j hj
      by_cases hji : j=i
      · subst j; simp
      · rw [Function.update_of_ne hji]
        exact hs j (List.mem_cons_of_mem _ hj)
    obtain ⟨t,ht,htb⟩ := ih (Function.update s i []) ht
    refine ⟨(s i).length+1+t+2,?_,?_⟩
    · rw [clearList,eraseStore_cons]
      exact seq_executes _ _ g (clear_executes g i s) ht
    · have hi := hs i (by simp)
      simp only [List.length_cons,Nat.add_mul]
      omega

end HiddenCircuits.GraphReduction.Runtime
