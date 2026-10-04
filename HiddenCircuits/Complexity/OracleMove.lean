import HiddenCircuits.Complexity.OracleResult

/-! Frame-preserving movement of a runtime bit string, with exact real cost. -/
namespace HiddenCircuits.Complexity.OracleBlock
variable {k : ℕ}

noncomputable def moveOn (source target temp : Fin (k+1))
    (hst : source≠target) (hsw : source≠temp) (htw : target≠temp) : OracleBlock k :=
  seq (copyOn source target temp hst hsw htw) (clear source)

/-- Move onto a possibly nonempty target; source and temporary stack finish empty. -/
theorem moveOn_executes (g : BitString → ℕ) (source target temp : Fin (k+1))
    (hst : source≠target) (hsw : source≠temp) (htw : target≠temp)
    (s : Store k) (hw : s temp=[]) :
    (moveOn source target temp hst hsw htw).Executes g s
      (Function.update (Function.update s target (s source++s target)) source [])
      (6*(s source).length+5) := by
  have hc := copyOn_executes g source target temp hst hsw htw s hw
  have hd := clear_executes g source (Function.update s target (s source++s target))
  have he := seq_executes _ _ g hc hd
  convert he using 1
  simp only [Function.update_of_ne hst]
  omega

lemma moveOn_queryFree (source target temp : Fin (k+1))
    (hst : source≠target) (hsw : source≠temp) (htw : target≠temp) :
    (moveOn source target temp hst hsw htw).QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (clear_queryFree _)

/-- A clean binary operation can be plugged into arbitrary surrounding storage.
Only its first two data ports change; all work and external stacks are restored. -/
theorem rename_binary_executes {l : ℕ} (B : OracleBlock (k+1))
    (φ : Fin (k+2) ↪ Fin (l+1)) (g : BitString → ℕ)
    (outer : Store l) (x y z : BitString) (cost : ℕ)
    (h : B.Executes g (binaryStore x y) (binaryStore z []) cost)
    (hS : outer ∘ φ = binaryStore x y) :
    (rename B φ).Executes g outer
      (Function.update (Function.update outer (φ 0) z) (φ 1) []) cost := by
  apply rename_executes_to B φ g h hS
  · funext i
    have hs := congrFun hS i
    change outer (φ i)=binaryStore x y i at hs
    by_cases hi : i=0
    · subst i;simp [binaryStore,φ.injective.ne (show (0 : Fin (k+2)) ≠ 1 by intro h;have := congrArg Fin.val h;simp at this)]
    · by_cases hj : i=1
      · subst i;simp [binaryStore]
      · simp [Function.update_of_ne (φ.injective.ne hi),Function.update_of_ne (φ.injective.ne hj),
          binaryStore,hi,hj] at hs ⊢
        exact hs
  · intro j hj
    simp [Function.update_of_ne (Ne.symm (hj 0)),Function.update_of_ne (Ne.symm (hj 1))]

end HiddenCircuits.Complexity.OracleBlock
