import HiddenCircuits.Complexity.CanonicalSubstitution.Stores

/-! The existing inclusive grid loop on the enlarged, disjoint register space. -/
namespace HiddenCircuits.Complexity.CanonicalSubstitution
open OracleBlock
variable {k : ℕ}

def widenFrame (d : GridRuntime.Frame 34) : GridRuntime.Frame (k+35) := fun q =>
  if h : q.val<34 then d ⟨q.val,h⟩ else []

lemma extend_grid_store (n m i j : ℕ) (inner outer : BitString) (d : GridRuntime.Frame 34) :
    extend (k := k) (GridRuntime.store n m i j inner outer d)=
      GridRuntime.store n m i j inner outer (widenFrame d) := by
  apply wide_ext
  · intro q
    rw [extend_base]
    fin_cases q <;> rfl
  · intro q
    rw [extend_work]
    have h₀ : ¬43+q.val<9 := by omega
    have h₁ : ¬(43+q.val)-9<34 := by omega
    simp [GridRuntime.store,workEmbedding,widenFrame,h₀,h₁,
      show 43+q.val≠0 by omega,show 43+q.val≠1 by omega,show 43+q.val≠2 by omega,
      show 43+q.val≠3 by omega,show 43+q.val≠4 by omega,show 43+q.val≠5 by omega,
      show 43+q.val≠6 by omega,show 43+q.val≠7 by omega]

lemma extend_grid_initial (n m : ℕ) (d : GridRuntime.Frame 34) :
    extend (k := k) (GridRuntime.initialStore n m d)=GridRuntime.initialStore n m (widenFrame d) := by
  apply wide_ext
  · intro q
    rw [extend_base]
    fin_cases q <;> rfl
  · intro q
    rw [extend_work]
    have h₁ : ¬(43+q.val)-9<34 := by omega
    simp [GridRuntime.initialStore,workEmbedding,widenFrame,h₁,show 43+q.val≠0 by omega,show 43+q.val≠1 by omega]

end HiddenCircuits.Complexity.CanonicalSubstitution
