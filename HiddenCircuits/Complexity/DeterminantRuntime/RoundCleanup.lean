import HiddenCircuits.Complexity.DeterminantRuntime.RoundLayout

/-! Actual clearing and transfer of one round's output, with every bit charged. -/
namespace HiddenCircuits.Complexity.DeterminantRuntime.Round
open OracleBlock

noncomputable def cleanup : OracleBlock 30 := seq (clear 2) (seq (clear 3)
  (seq (clear 6) (seq (clear 7)
    (seq (moveOn 9 2 10 (by decide) (by decide) (by decide))
      (moveOn 8 3 10 (by decide) (by decide) (by decide))))))

theorem cleanup_executes (g : BitString → ℕ) (n : ℕ) (a b c : BitString) (k clock : ℕ)
    (product trace nextCoefficient nextMatrix : BitString) :
    cleanup.Executes g (state n a b c k clock product trace nextCoefficient nextMatrix)
      (store n a nextMatrix nextCoefficient k clock)
      (b.length+c.length+product.length+trace.length+6*nextMatrix.length+6*nextCoefficient.length+24) := by
  let s0 := state n a b c k clock product trace nextCoefficient nextMatrix
  let s1 := state n a [] c k clock product trace nextCoefficient nextMatrix
  let s2 := state n a [] [] k clock product trace nextCoefficient nextMatrix
  let s3 := state n a [] [] k clock [] trace nextCoefficient nextMatrix
  let s4 := state n a [] [] k clock [] [] nextCoefficient nextMatrix
  let s5 := state n a nextMatrix [] k clock [] [] nextCoefficient []
  have h1 : (clear (2 : Fin 31)).Executes g s0 s1 (b.length+1) := by
    convert clear_executes g (2 : Fin 31) s0 using 1
    funext q; fin_cases q <;> rfl
  have h2 : (clear (3 : Fin 31)).Executes g s1 s2 (c.length+1) := by
    convert clear_executes g (3 : Fin 31) s1 using 1
    funext q; fin_cases q <;> rfl
  have h3 : (clear (6 : Fin 31)).Executes g s2 s3 (product.length+1) := by
    convert clear_executes g (6 : Fin 31) s2 using 1
    funext q; fin_cases q <;> rfl
  have h4 : (clear (7 : Fin 31)).Executes g s3 s4 (trace.length+1) := by
    convert clear_executes g (7 : Fin 31) s3 using 1
    funext q; fin_cases q <;> rfl
  have h5 : (moveOn (9 : Fin 31) 2 10 (by decide) (by decide) (by decide)).Executes g s4 s5
      (6*nextMatrix.length+5) := by
    convert moveOn_executes g (9 : Fin 31) 2 10 (by decide) (by decide) (by decide) s4 rfl using 1
    funext q; fin_cases q <;> simp [s4,s5,state]
  have h6 : (moveOn (8 : Fin 31) 3 10 (by decide) (by decide) (by decide)).Executes g s5
      (store n a nextMatrix nextCoefficient k clock) (6*nextCoefficient.length+5) := by
    convert moveOn_executes g (8 : Fin 31) 3 10 (by decide) (by decide) (by decide) s5 rfl using 1
    funext q; fin_cases q <;> simp [s5,store,state]
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3
    (seq_executes _ _ g h4 (seq_executes _ _ g h5 h6)))) using 1 <;> omega

theorem cleanup_queryFree : cleanup.QueryFree := seq_queryFree _ _ (clear_queryFree _)
  (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (clear_queryFree _)
    (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _)
      (moveOn_queryFree _ _ _ _ _ _)))))

end HiddenCircuits.Complexity.DeterminantRuntime.Round
