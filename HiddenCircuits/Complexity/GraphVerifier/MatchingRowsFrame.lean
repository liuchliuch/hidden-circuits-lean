import HiddenCircuits.Complexity.GraphVerifier.MatchingRowsRuntime

/-! Full frame for the real matching-certificate exactly-one row pass. -/
namespace HiddenCircuits.Complexity.GraphVerifier.MatchingRuntime
open OracleBlock

noncomputable def oneRowsOn {k : ℕ} (φ : Fin 6 ↪ Fin (k+1)) : OracleBlock k := rename oneRowsBlock φ

theorem oneRowsOn_executes {k : ℕ} (φ : Fin 6 ↪ Fin (k+1)) (g : BitString → ℕ)
    (s : Store k) (n : ℕ) (w : BitString) (a : Bool) (hw : n*n≤w.length)
    (hs : s∘φ=oneRowsStore n [] w [a] []) :
    (oneRowsOn φ).Executes g s
      (Function.update (Function.update s (φ 2) (w.drop (n*n))) (φ 3) [allRowsValue n w 0 n a])
      (7*n*n+14*n+5) := by
  apply rename_executes_to oneRowsBlock φ g (oneRows_executes g n w a hw) hs
  · have he : (Function.update (Function.update s (φ 2) (w.drop (n*n))) (φ 3) [allRowsValue n w 0 n a])∘φ=
        Function.update (Function.update (s∘φ) 2 (w.drop (n*n))) 3 [allRowsValue n w 0 n a] := by
      funext i;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i;fin_cases i <;> rfl
  · intro j hj
    rw [Function.update_of_ne (hj 3).symm,Function.update_of_ne (hj 2).symm]

theorem oneRowsOn_queryFree {k : ℕ} (φ : Fin 6 ↪ Fin (k+1)) : (oneRowsOn φ).QueryFree :=
  rename_queryFree _ _ oneRows_queryFree
end HiddenCircuits.Complexity.GraphVerifier.MatchingRuntime
