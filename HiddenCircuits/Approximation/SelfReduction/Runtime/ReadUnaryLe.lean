import HiddenCircuits.Approximation.SelfReduction.Runtime.UnaryLe

/-! A read-only unary comparator with a clean work area and explicit frames. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

abbrev readLeStore := GraphVerifier.Runtime.readLengthStore
abbrev readLeEmbedding := GraphVerifier.Runtime.readLengthEmbedding

noncomputable def readUnaryLe : OracleBlock 5 :=
  seq (copyOn 0 3 5 (by decide) (by decide) (by decide))
    (seq (copyOn 1 4 5 (by decide) (by decide) (by decide)) (rename unaryLe readLeEmbedding))

theorem readUnaryLe_executes (g : BitString → ℕ) (a b out : BitString) :
    ∃ t, readUnaryLe.Executes g (readLeStore a b out [] [] [])
      (readLeStore a b (decide (a.length ≤ b.length)::out) [] [] []) t ∧
      t ≤ 8*(a.length+b.length)+17 := by
  have h1 : (copyOn (0 : Fin 6) 3 5 (by decide) (by decide) (by decide)).Executes g
      (readLeStore a b out [] [] []) (readLeStore a b out a [] []) (5*a.length+2) := by
    convert copyOn_executes g (0 : Fin 6) 3 5 (by decide) (by decide) (by decide)
      (readLeStore a b out [] [] []) rfl using 1
    funext i; fin_cases i <;> simp [readLeStore, GraphVerifier.Runtime.readLengthStore]
  have h2 : (copyOn (1 : Fin 6) 4 5 (by decide) (by decide) (by decide)).Executes g
      (readLeStore a b out a [] []) (readLeStore a b out a b []) (5*b.length+2) := by
    convert copyOn_executes g (1 : Fin 6) 4 5 (by decide) (by decide) (by decide)
      (readLeStore a b out a [] []) rfl using 1
    funext i; fin_cases i <;> simp [readLeStore, GraphVerifier.Runtime.readLengthStore]
  obtain ⟨t,ht,hb⟩ := unaryLe_executes g a b out
  have h3 : (rename unaryLe readLeEmbedding).Executes g
      (readLeStore a b out a b []) (readLeStore a b (decide (a.length ≤ b.length)::out) [] [] []) t := by
    apply rename_executes_to unaryLe readLeEmbedding g ht
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
    · intro j hj
      fin_cases j
      all_goals first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) | exact False.elim (hj 2 rfl)
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 h3),?_⟩
  omega

 theorem readUnaryLe_queryFree : readUnaryLe.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (rename_queryFree _ _ unaryLe_queryFree))

noncomputable def readUnaryLeOn {k : ℕ} (φ : Fin 6 ↪ Fin (k+1)) : OracleBlock k :=
  rename readUnaryLe φ

/-- The routine can be placed inside arbitrary stores while preserving every
undeclared port, including the original operands. -/
theorem readUnaryLeOn_executes {k : ℕ} (φ : Fin 6 ↪ Fin (k+1)) (g : BitString → ℕ)
    (s : Store k) (a b out : BitString) (hs : s∘φ=readLeStore a b out [] [] []) :
    ∃ t, (readUnaryLeOn φ).Executes g s
      (Function.update s (φ 2) (decide (a.length ≤ b.length)::out)) t ∧
      t ≤ 8*(a.length+b.length)+17 := by
  obtain ⟨t,ht,hb⟩ := readUnaryLe_executes g a b out
  refine ⟨t,?_,hb⟩
  apply rename_executes_to readUnaryLe φ g ht hs
  · have he : (Function.update s (φ 2) (decide (a.length ≤ b.length)::out))∘φ =
        Function.update (s∘φ) 2 (decide (a.length ≤ b.length)::out) := by
      funext i; simp [Function.comp_def, Function.update_apply, φ.injective.eq_iff]
    rw [he, hs]
    funext i; fin_cases i <;> rfl
  · intro j hj
    exact Function.update_of_ne (hj 2).symm _ _

 theorem readUnaryLeOn_queryFree {k : ℕ} (φ : Fin 6 ↪ Fin (k+1)) :
    (readUnaryLeOn φ).QueryFree := rename_queryFree _ _ readUnaryLe_queryFree

end HiddenCircuits.Approximation.SelfReduction.Runtime
