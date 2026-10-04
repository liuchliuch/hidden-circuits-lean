import HiddenCircuits.Complexity.GraphVerifier.DropClock
import HiddenCircuits.Complexity.GraphVerifier.BitChecks

/-! Actual read-only false-padding validation of the certificate suffix. -/
namespace HiddenCircuits.Complexity.GraphVerifier.Runtime
open OracleBlock

def paddingStore (n : ℕ) (w out copy clock temp : BitString) : Store 5 := fun i =>
  if i.val=0 then List.replicate n true else if i.val=1 then w else if i.val=2 then out
  else if i.val=3 then copy else if i.val=4 then clock else temp

def paddingDropEmbedding : Fin 2 ↪ Fin 6 where
  toFun i := if i.val=0 then 3 else 4
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
 def paddingCheckEmbedding : Fin 1 ↪ Fin 6 := ⟨fun _ => 3,fun _ _ _ => Subsingleton.elim _ _⟩

noncomputable def paddingBlock : OracleBlock 5 :=
  seq (copyOn 1 3 5 (by decide) (by decide) (by decide))
    (seq (copyOn 0 4 5 (by decide) (by decide) (by decide))
      (seq (rename dropClockBlock paddingDropEmbedding)
        (seq (rename (BitChecks.block false) paddingCheckEmbedding) (reverseOn 3 2 (by decide)))))

 theorem padding_executes (g : BitString → ℕ) (n : ℕ) (w : BitString) :
    ∃ cost, paddingBlock.Executes g (paddingStore n w [] [] [] [])
      (paddingStore n w [(w.drop n).all (fun b => !b)] [] [] []) cost ∧
      cost≤6*w.length+8*n+18 := by
  let d := (w.drop n).all (fun b => !b)
  let s₀ := paddingStore n w [] [] [] []
  let s₁ := paddingStore n w [] w [] []
  let s₂ := paddingStore n w [] w (List.replicate n true) []
  let s₃ := paddingStore n w [] (w.drop n) [] []
  let s₄ := paddingStore n w [] [d] [] []
  let s₅ := paddingStore n w [d] [] [] []
  have h₁ : (copyOn (1:Fin 6) 3 5 (by decide) (by decide) (by decide)).Executes g s₀ s₁ (5*w.length+2) := by
    convert copyOn_executes g (1:Fin 6) 3 5 (by decide) (by decide) (by decide) s₀ rfl using 1
    funext i;fin_cases i <;> simp [s₀,s₁,paddingStore]
  have h₂ : (copyOn (0:Fin 6) 4 5 (by decide) (by decide) (by decide)).Executes g s₁ s₂ (5*n+2) := by
    convert copyOn_executes g (0:Fin 6) 4 5 (by decide) (by decide) (by decide) s₁ rfl using 1
    · funext i;fin_cases i <;> simp [s₁,s₂,paddingStore]
    · simp [s₁,paddingStore]
  have h₃ : (rename dropClockBlock paddingDropEmbedding).Executes g s₂ s₃ (3*n+1) := by
    have hh := dropClock_execution g w (List.replicate n true)
    simp only [List.length_replicate] at hh
    apply rename_executes_to dropClockBlock paddingDropEmbedding g hh
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi
      fin_cases i
      all_goals first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl)
  have h₄ : (rename (BitChecks.block false) paddingCheckEmbedding).Executes g s₃ s₄ ((w.drop n).length+2) := by
    have hh := BitChecks.block_executes g false (w.drop n)
    have he : (fun b : Bool => b==false)=(fun b : Bool => !b) := by funext b;cases b <;> rfl
    rw [he] at hh
    apply rename_executes_to (BitChecks.block false) paddingCheckEmbedding g hh
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi
      fin_cases i
      all_goals first | rfl | exact False.elim (hi 0 rfl)
  have h₅ : (reverseOn (3:Fin 6) 2 (by decide)).Executes g s₄ s₅ 3 := by
    convert reverseOn_executes g (3:Fin 6) 2 (by decide) s₄ using 1
    funext i;fin_cases i <;> simp [s₄,s₅,paddingStore]
  refine ⟨(5*w.length+2)+((5*n+2)+((3*n+1)+(((w.drop n).length+2)+3+2)+2)+2)+2,
    seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ (seq_executes _ _ g h₄ h₅))),?_⟩
  simp only [List.length_drop]
  omega

 theorem padding_queryFree : paddingBlock.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (rename_queryFree _ _ dropClock_queryFree)
      (seq_queryFree _ _ (rename_queryFree _ _ (BitChecks.block_queryFree false)) (reverseOn_queryFree _ _ _))))

noncomputable def paddingOn {k : ℕ} (φ : Fin 6 ↪ Fin (k+1)) : OracleBlock k := rename paddingBlock φ

theorem paddingOn_executes {k : ℕ} (φ : Fin 6 ↪ Fin (k+1)) (g : BitString → ℕ)
    (s : Store k) (n : ℕ) (w : BitString) (hs : s∘φ=paddingStore n w [] [] [] []) :
    ∃ cost, (paddingOn φ).Executes g s (Function.update s (φ 2) [(w.drop n).all (fun b => !b)]) cost ∧
      cost≤6*w.length+8*n+18 := by
  obtain ⟨c,hc,hb⟩ := padding_executes g n w
  refine ⟨c,?_,hb⟩
  apply rename_executes_to paddingBlock φ g hc hs
  · have he : (Function.update s (φ 2) [(w.drop n).all (fun b => !b)])∘φ=
        Function.update (s∘φ) 2 [(w.drop n).all (fun b => !b)] := by
      funext i;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i;fin_cases i <;> rfl
  · intro j hj
    exact Function.update_of_ne (hj 2).symm _ _

theorem paddingOn_queryFree {k : ℕ} (φ : Fin 6 ↪ Fin (k+1)) : (paddingOn φ).QueryFree :=
  rename_queryFree _ _ padding_queryFree

end HiddenCircuits.Complexity.GraphVerifier.Runtime
