import HiddenCircuits.Complexity.GraphVerifier.UnaryProduct
import HiddenCircuits.Complexity.GraphVerifier.PaddingRuntime
import HiddenCircuits.Complexity.GraphVerifier.SquareLength

/-! Actual false-padding guard after n² certificate entries, using unary multiplication. -/
namespace HiddenCircuits.Complexity.GraphVerifier.Runtime
open OracleBlock

def squarePaddingStore (n : ℕ) (payload out square counter temp left right : BitString) : Store 7 := fun i =>
  if i.val=0 then List.replicate n true else if i.val=1 then payload else if i.val=2 then out
  else if i.val=3 then square else if i.val=4 then counter else if i.val=5 then temp
  else if i.val=6 then left else right

def squarePaddingProductEmbedding : Fin 4 ↪ Fin 8 where
  toFun i := if i.val=0 then 0 else if i.val=1 then 4 else if i.val=2 then 3 else 5
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
 def squarePaddingEmbedding : Fin 6 ↪ Fin 8 where
  toFun i := if i.val=0 then 3 else if i.val=1 then 1 else if i.val=2 then 2
    else if i.val=3 then 6 else if i.val=4 then 7 else 5
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

noncomputable def squarePaddingBlock : OracleBlock 7 :=
  seq (copyOn 0 4 5 (by decide) (by decide) (by decide))
    (seq (rename repeatCopyBlock squarePaddingProductEmbedding) (seq (paddingOn squarePaddingEmbedding) (clear 3)))

 theorem squarePadding_executes (g : BitString → ℕ) (n : ℕ) (payload : BitString) :
    ∃ cost, squarePaddingBlock.Executes g (squarePaddingStore n payload [] [] [] [] [] [])
      (squarePaddingStore n payload [(payload.drop (n*n)).all (fun b => !b)] [] [] [] [] []) cost ∧
      cost≤14*n^2+9*n+6*payload.length+28 := by
  let u := List.replicate n true
  let q := List.replicate (n*n) true
  let s₀ := squarePaddingStore n payload [] [] [] [] [] []
  let s₁ := squarePaddingStore n payload [] [] u [] [] []
  let s₂ := squarePaddingStore n payload [] q [] [] [] []
  let s₃ := squarePaddingStore n payload [(payload.drop (n*n)).all (fun b => !b)] q [] [] [] []
  let s₄ := squarePaddingStore n payload [(payload.drop (n*n)).all (fun b => !b)] [] [] [] [] []
  have h₁ : (copyOn (0:Fin 8) 4 5 (by decide) (by decide) (by decide)).Executes g s₀ s₁ (5*n+2) := by
    convert copyOn_executes g (0:Fin 8) 4 5 (by decide) (by decide) (by decide) s₀ rfl using 1
    · funext i;fin_cases i <;> simp [s₀,s₁,squarePaddingStore,u]
    · simp [s₀,squarePaddingStore]
  have h₂ : (rename repeatCopyBlock squarePaddingProductEmbedding).Executes g s₁ s₂ (n*(5*n+4)+1) := by
    apply rename_executes_to repeatCopyBlock squarePaddingProductEmbedding g (unaryProduct_execution g n n)
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi
      fin_cases i
      all_goals first | rfl | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl)
  obtain ⟨c,hc,hcb⟩ := paddingOn_executes squarePaddingEmbedding g s₂ (n*n) payload
    (by funext i;fin_cases i <;> rfl)
  have h₃ : (paddingOn squarePaddingEmbedding).Executes g s₂ s₃ c := by
    convert hc using 1
    funext i;fin_cases i <;> simp [s₂,s₃,squarePaddingStore,squarePaddingEmbedding]
  have h₄ : (clear (3:Fin 8)).Executes g s₃ s₄ (n*n+1) := by
    convert clear_executes g (3:Fin 8) s₃ using 1
    · funext i;fin_cases i <;> rfl
    · simp [s₃,squarePaddingStore,q]
  refine ⟨(5*n+2)+((n*(5*n+4)+1)+(c+(n*n+1)+2)+2)+2,
    seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ h₄)),?_⟩
  nlinarith

 theorem squarePadding_queryFree : squarePaddingBlock.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (rename_queryFree _ _ repeatCopy_queryFree)
    (seq_queryFree _ _ (paddingOn_queryFree _) (clear_queryFree _)))

noncomputable def squarePaddingOn {k : ℕ} (φ : Fin 8 ↪ Fin (k+1)) : OracleBlock k := rename squarePaddingBlock φ

theorem squarePaddingOn_executes {k : ℕ} (φ : Fin 8 ↪ Fin (k+1)) (g : BitString → ℕ)
    (s : Store k) (n : ℕ) (payload : BitString) (hs : s∘φ=squarePaddingStore n payload [] [] [] [] [] []) :
    ∃ cost, (squarePaddingOn φ).Executes g s (Function.update s (φ 2) [(payload.drop (n*n)).all (fun b => !b)]) cost ∧
      cost≤14*n^2+9*n+6*payload.length+28 := by
  obtain ⟨c,hc,hb⟩ := squarePadding_executes g n payload
  refine ⟨c,?_,hb⟩
  apply rename_executes_to squarePaddingBlock φ g hc hs
  · have he : (Function.update s (φ 2) [(payload.drop (n*n)).all (fun b => !b)])∘φ=
        Function.update (s∘φ) 2 [(payload.drop (n*n)).all (fun b => !b)] := by
      funext i;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i;fin_cases i <;> rfl
  · intro j hj
    exact Function.update_of_ne (hj 2).symm _ _

theorem squarePaddingOn_queryFree {k : ℕ} (φ : Fin 8 ↪ Fin (k+1)) : (squarePaddingOn φ).QueryFree :=
  rename_queryFree _ _ squarePadding_queryFree

end HiddenCircuits.Complexity.GraphVerifier.Runtime
