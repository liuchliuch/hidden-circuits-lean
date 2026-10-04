import HiddenCircuits.Complexity.CNFCloneEmitter.UnarySplit
import HiddenCircuits.Complexity.GraphVerifier.ReadOnlyLength

/-! Read-only unary strict comparison, using the actual consuming split program. -/
namespace HiddenCircuits.GraphReduction.Runtime
open Complexity Complexity.OracleBlock

 def compareStore (x y : ℕ) (out : BitString) : Store 5 := fun i =>
  if i.val=0 then List.replicate x true else if i.val=1 then List.replicate y true else if i.val=2 then out else []
 def compareEmbedding : Fin 3 ↪ Fin 6 where
  toFun i := if i.val=0 then 3 else if i.val=1 then 4 else 2
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all
 noncomputable def readOnlyLT : OracleBlock 5 :=
  seq (copyOn 0 3 5 (by decide) (by decide) (by decide))
    (seq (copyOn 1 4 5 (by decide) (by decide) (by decide))
      (seq (rename CNFCloneEmitter.UnarySplit.program compareEmbedding) (clear 3)))

 theorem readOnlyLT_executes (g : BitString → ℕ) (x y : ℕ) :
    ∃ t, readOnlyLT.Executes g (compareStore x y []) (compareStore x y [decide (x<y)]) t ∧
      t≤6*x+14*y+15 := by
  let s1 : Store 5 := fun i => if i.val=3 then List.replicate x true else compareStore x y [] i
  let s2 : Store 5 := fun i => if i.val=4 then List.replicate y true else s1 i
  let s3 : Store 5 := fun i => if i.val=3 then List.replicate (x-y) true else compareStore x y [decide (x<y)] i
  have h1 : (copyOn (0 : Fin 6) 3 5 (by decide) (by decide) (by decide)).Executes g
      (compareStore x y []) s1 (5*x+2) := by
    convert copyOn_executes g (0 : Fin 6) 3 5 (by decide) (by decide) (by decide) (compareStore x y []) rfl using 1
    · funext i; fin_cases i <;> simp [compareStore,s1]
    · simp [compareStore]
  have h2 : (copyOn (1 : Fin 6) 4 5 (by decide) (by decide) (by decide)).Executes g s1 s2 (5*y+2) := by
    convert copyOn_executes g (1 : Fin 6) 4 5 (by decide) (by decide) (by decide) s1 rfl using 1
    · funext i; fin_cases i <;> simp [compareStore,s1,s2]
    · simp [compareStore,s1]
  obtain ⟨c,hc,hcb⟩ := CNFCloneEmitter.UnarySplit.program_executes g x y
  have h3 : (rename CNFCloneEmitter.UnarySplit.program compareEmbedding).Executes g s2 s3 c := by
    apply rename_executes_to CNFCloneEmitter.UnarySplit.program compareEmbedding g hc
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
    · intro i hi; fin_cases i <;> first | rfl | (exfalso; exact hi 0 rfl) | (exfalso; exact hi 1 rfl) | (exfalso; exact hi 2 rfl)
  have h4 : (clear (3 : Fin 6)).Executes g s3 (compareStore x y [decide (x<y)]) (x-y+1) := by
    convert clear_executes g (3 : Fin 6) s3 using 1
    · funext i; fin_cases i <;> rfl
    · simp [s3]
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)),?_⟩
  omega

 lemma readOnlyLT_queryFree : readOnlyLT.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
      (seq_queryFree _ _ (rename_queryFree _ _ CNFCloneEmitter.UnarySplit.program_queryFree) (clear_queryFree _)))

 noncomputable def readOnlyLTOn {k : ℕ} (φ : Fin 6 ↪ Fin (k+1)) : OracleBlock k := rename readOnlyLT φ
 theorem readOnlyLTOn_executes {k : ℕ} (φ : Fin 6 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (x y : ℕ) (hs : s∘φ=compareStore x y []) :
    ∃ t, (readOnlyLTOn φ).Executes g s (Function.update s (φ 2) [decide (x<y)]) t ∧ t≤6*x+14*y+15 := by
  obtain ⟨t,ht,hb⟩ := readOnlyLT_executes g x y
  refine ⟨t,?_,hb⟩
  apply rename_executes_to readOnlyLT φ g ht hs
  · have he : (Function.update s (φ 2) [decide (x<y)])∘φ = Function.update (s∘φ) 2 [decide (x<y)] := by
      funext i; simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i; fin_cases i <;> rfl
  · intro i hi; exact Function.update_of_ne (hi 2).symm _ _
 lemma readOnlyLTOn_queryFree {k : ℕ} (φ : Fin 6 ↪ Fin (k+1)) : (readOnlyLTOn φ).QueryFree :=
  rename_queryFree _ _ readOnlyLT_queryFree

end HiddenCircuits.GraphReduction.Runtime
