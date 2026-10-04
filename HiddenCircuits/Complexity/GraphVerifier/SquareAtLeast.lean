import HiddenCircuits.Complexity.GraphVerifier.UnaryProduct
import HiddenCircuits.Complexity.GraphVerifier.ReadOnlyAtLeast

/-! Actual lower-bound n²-payload-length guard, using unary multiplication and copied length comparison. -/
namespace HiddenCircuits.Complexity.GraphVerifier.Runtime
open OracleBlock

def squareAtLeastStore (n : ℕ) (payload out square counter temp left right : BitString) : Store 7 := fun i =>
  if i.val=0 then List.replicate n true else if i.val=1 then payload else if i.val=2 then out
  else if i.val=3 then square else if i.val=4 then counter else if i.val=5 then temp
  else if i.val=6 then left else right

def squareAtLeastProductEmbedding : Fin 4 ↪ Fin 8 where
  toFun i := if i.val=0 then 0 else if i.val=1 then 4 else if i.val=2 then 3 else 5
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
 def squareAtLeastEmbedding : Fin 6 ↪ Fin 8 where
  toFun i := if i.val=0 then 1 else if i.val=1 then 3 else if i.val=2 then 2
    else if i.val=3 then 6 else if i.val=4 then 7 else 5
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

noncomputable def squareAtLeastBlock : OracleBlock 7 :=
  seq (copyOn 0 4 5 (by decide) (by decide) (by decide))
    (seq (rename repeatCopyBlock squareAtLeastProductEmbedding) (seq (readAtLeastOn squareAtLeastEmbedding) (clear 3)))

 theorem squareAtLeast_executes (g : BitString → ℕ) (n : ℕ) (payload : BitString) :
    ∃ cost, squareAtLeastBlock.Executes g (squareAtLeastStore n payload [] [] [] [] [] [])
      (squareAtLeastStore n payload [decide (n*n≤payload.length)] [] [] [] [] []) cost ∧
      cost≤19*n^2+9*n+13*payload.length+33 := by
  let u := List.replicate n true
  let q := List.replicate (n*n) true
  let s₀ := squareAtLeastStore n payload [] [] [] [] [] []
  let s₁ := squareAtLeastStore n payload [] [] u [] [] []
  let s₂ := squareAtLeastStore n payload [] q [] [] [] []
  let s₃ := squareAtLeastStore n payload [decide (n*n≤payload.length)] q [] [] [] []
  let s₄ := squareAtLeastStore n payload [decide (n*n≤payload.length)] [] [] [] [] []
  have h₁ : (copyOn (0:Fin 8) 4 5 (by decide) (by decide) (by decide)).Executes g s₀ s₁ (5*n+2) := by
    convert copyOn_executes g (0:Fin 8) 4 5 (by decide) (by decide) (by decide) s₀ rfl using 1
    · funext i;fin_cases i <;> simp [s₀,s₁,squareAtLeastStore,u]
    · simp [s₀,squareAtLeastStore]
  have h₂ : (rename repeatCopyBlock squareAtLeastProductEmbedding).Executes g s₁ s₂ (n*(5*n+4)+1) := by
    apply rename_executes_to repeatCopyBlock squareAtLeastProductEmbedding g (unaryProduct_execution g n n)
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi
      fin_cases i
      all_goals first | rfl | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl)
  obtain ⟨c,hc,hcb⟩ := readAtLeastOn_executes squareAtLeastEmbedding g s₂ payload q
    (by funext i;fin_cases i <;> rfl)
  have h₃ : (readAtLeastOn squareAtLeastEmbedding).Executes g s₂ s₃ c := by
    simp only [q,List.length_replicate] at hc
    convert hc using 1
    funext i;fin_cases i <;> simp [s₂,s₃,squareAtLeastStore,squareAtLeastEmbedding]
  have h₄ : (clear (3:Fin 8)).Executes g s₃ s₄ (n*n+1) := by
    convert clear_executes g (3:Fin 8) s₃ using 1
    · funext i;fin_cases i <;> rfl
    · simp [s₃,squareAtLeastStore,q]
  refine ⟨(5*n+2)+((n*(5*n+4)+1)+(c+(n*n+1)+2)+2)+2,
    seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ h₄)),?_⟩
  simp only [q,List.length_replicate] at hcb
  nlinarith

 theorem squareAtLeast_queryFree : squareAtLeastBlock.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (rename_queryFree _ _ repeatCopy_queryFree)
    (seq_queryFree _ _ (readAtLeastOn_queryFree _) (clear_queryFree _)))

noncomputable def squareAtLeastOn {k : ℕ} (φ : Fin 8 ↪ Fin (k+1)) : OracleBlock k := rename squareAtLeastBlock φ

theorem squareAtLeastOn_executes {k : ℕ} (φ : Fin 8 ↪ Fin (k+1)) (g : BitString → ℕ)
    (s : Store k) (n : ℕ) (payload : BitString) (hs : s∘φ=squareAtLeastStore n payload [] [] [] [] [] []) :
    ∃ cost, (squareAtLeastOn φ).Executes g s (Function.update s (φ 2) [decide (n*n≤payload.length)]) cost ∧
      cost≤19*n^2+9*n+13*payload.length+33 := by
  obtain ⟨c,hc,hb⟩ := squareAtLeast_executes g n payload
  refine ⟨c,?_,hb⟩
  apply rename_executes_to squareAtLeastBlock φ g hc hs
  · have he : (Function.update s (φ 2) [decide (n*n≤payload.length)])∘φ=
        Function.update (s∘φ) 2 [decide (n*n≤payload.length)] := by
      funext i;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i;fin_cases i <;> rfl
  · intro j hj
    exact Function.update_of_ne (hj 2).symm _ _

theorem squareAtLeastOn_queryFree {k : ℕ} (φ : Fin 8 ↪ Fin (k+1)) : (squareAtLeastOn φ).QueryFree :=
  rename_queryFree _ _ squareAtLeast_queryFree

end HiddenCircuits.Complexity.GraphVerifier.Runtime
