import HiddenCircuits.Complexity.CNFCloneEmitter.ClauseLookup

/-! Read-only indexed structural-descriptor lookup by literal bit instructions. -/
namespace HiddenCircuits.GraphReduction.Runtime
open Complexity Complexity.OracleBlock

 def lookupStore (data index output : BitString) : Store 6 := fun i =>
  if i.val=0 then data else if i.val=1 then index else if i.val=2 then output else []
 def lookupEmbedding : Fin 5 ↪ Fin 7 where
  toFun i := if i.val=0 then 3 else if i.val=1 then 4 else if i.val=2 then 2 else if i.val=3 then 5 else 6
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all
 noncomputable def listLookup : OracleBlock 6 :=
  seq (copyOn 0 3 5 (by decide) (by decide) (by decide))
    (seq (copyOn 1 4 5 (by decide) (by decide) (by decide))
      (rename CNFCloneEmitter.ClauseLookup.program lookupEmbedding))
 def lookupBound (length index : ℕ) := 5*length+5*index+(index+1)*(6*length+14)+9

 theorem listLookup_executes (g : BitString → ℕ) (ws : List BitString) (j : ℕ) :
    ∃ t, listLookup.Executes g (lookupStore (encodeBitList ws) (List.replicate j true) [])
      (lookupStore (encodeBitList ws) (List.replicate j true) (ws[j]?.getD [])) t ∧
      t≤lookupBound (encodeBitList ws).length j := by
  let s1 : Store 6 := fun i => if i.val=3 then encodeBitList ws else lookupStore (encodeBitList ws) (List.replicate j true) [] i
  let s2 : Store 6 := fun i => if i.val=4 then List.replicate j true else s1 i
  have h1 : (copyOn (0 : Fin 7) 3 5 (by decide) (by decide) (by decide)).Executes g
      (lookupStore (encodeBitList ws) (List.replicate j true) []) s1 (5*(encodeBitList ws).length+2) := by
    convert copyOn_executes g (0 : Fin 7) 3 5 (by decide) (by decide) (by decide)
      (lookupStore (encodeBitList ws) (List.replicate j true) []) rfl using 1
    funext i; fin_cases i <;> simp [s1,lookupStore]
  have h2 : (copyOn (1 : Fin 7) 4 5 (by decide) (by decide) (by decide)).Executes g s1 s2 (5*j+2) := by
    convert copyOn_executes g (1 : Fin 7) 4 5 (by decide) (by decide) (by decide) s1 rfl using 1
    · funext i; fin_cases i <;> simp [s2,s1,lookupStore]
    · simp [s1,lookupStore]
  obtain ⟨c,hc,hcb⟩ := CNFCloneEmitter.ClauseLookup.program_executes g ws j
  have h3 : (rename CNFCloneEmitter.ClauseLookup.program lookupEmbedding).Executes g s2
      (lookupStore (encodeBitList ws) (List.replicate j true) (ws[j]?.getD [])) c := by
    apply rename_executes_to CNFCloneEmitter.ClauseLookup.program lookupEmbedding g hc
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
    · intro i hi; fin_cases i <;> first | rfl | (exfalso; exact hi 0 rfl) | (exfalso; exact hi 1 rfl) | (exfalso; exact hi 2 rfl)
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 h3),?_⟩
  unfold lookupBound
  omega

 theorem listLookup_in_range (g : BitString → ℕ) (ws : List BitString) (j : Fin ws.length) :
    ∃ t, listLookup.Executes g (lookupStore (encodeBitList ws) (List.replicate j.val true) [])
      (lookupStore (encodeBitList ws) (List.replicate j.val true) (ws.get j)) t ∧
      t≤lookupBound (encodeBitList ws).length j.val := by
  simpa [List.getElem?_eq_getElem,j.isLt] using listLookup_executes g ws j.val

 lemma listLookup_queryFree : listLookup.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
      (rename_queryFree _ _ CNFCloneEmitter.ClauseLookup.program_queryFree))

 noncomputable def listLookupOn {k : ℕ} (φ : Fin 7 ↪ Fin (k+1)) : OracleBlock k := rename listLookup φ
 theorem listLookupOn_executes {k : ℕ} (φ : Fin 7 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (ws : List BitString) (j : ℕ) (hs : s∘φ=lookupStore (encodeBitList ws) (List.replicate j true) []) :
    ∃ t, (listLookupOn φ).Executes g s (Function.update s (φ 2) (ws[j]?.getD [])) t ∧
      t≤lookupBound (encodeBitList ws).length j := by
  obtain ⟨t,ht,hb⟩ := listLookup_executes g ws j
  refine ⟨t,?_,hb⟩
  apply rename_executes_to listLookup φ g ht hs
  · have he : (Function.update s (φ 2) (ws[j]?.getD []))∘φ =
        Function.update (s∘φ) 2 (ws[j]?.getD []) := by
      funext i; simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i; fin_cases i <;> rfl
  · intro i hi; exact Function.update_of_ne (hi 2).symm _ _
 lemma listLookupOn_queryFree {k : ℕ} (φ : Fin 7 ↪ Fin (k+1)) : (listLookupOn φ).QueryFree :=
  rename_queryFree _ _ listLookup_queryFree

end HiddenCircuits.GraphReduction.Runtime
