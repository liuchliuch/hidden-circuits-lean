import HiddenCircuits.GraphReduction.Runtime.ListLookup
import HiddenCircuits.Complexity.LooseWordLookup
namespace HiddenCircuits.GraphReduction.Runtime
open Complexity Complexity.OracleBlock
def rawLookupBound (length index : ℕ) := 5*length+5*index+(index+1)*(6*length+30)+12
 theorem listLookup_raw (g : BitString → ℕ) (xs : BitString) (j : ℕ) :
    ∃ t, listLookup.Executes g (lookupStore xs (List.replicate j true) [])
      (lookupStore xs (List.replicate j true) ((LooseWordList.words xs)[j]?.getD [])) t ∧
      t≤rawLookupBound xs.length j := by
  let s1 : Store 6 := fun i => if i.val=3 then xs else lookupStore xs (List.replicate j true) [] i
  let s2 : Store 6 := fun i => if i.val=4 then List.replicate j true else s1 i
  have h1 : (copyOn (0 : Fin 7) 3 5 (by decide) (by decide) (by decide)).Executes g
      (lookupStore xs (List.replicate j true) []) s1 (5*xs.length+2) := by
    convert copyOn_executes g (0 : Fin 7) 3 5 (by decide) (by decide) (by decide)
      (lookupStore xs (List.replicate j true) []) rfl using 1
    funext i; fin_cases i <;> simp [s1,lookupStore]
  have h2 : (copyOn (1 : Fin 7) 4 5 (by decide) (by decide) (by decide)).Executes g s1 s2 (5*j+2) := by
    convert copyOn_executes g (1 : Fin 7) 4 5 (by decide) (by decide) (by decide) s1 rfl using 1
    · funext i; fin_cases i <;> simp [s2,s1,lookupStore]
    · simp [s1,lookupStore]
  obtain ⟨c,hc,hcb⟩ := CNFCloneEmitter.ClauseLookup.program_raw g xs j
  have h3 : (rename CNFCloneEmitter.ClauseLookup.program lookupEmbedding).Executes g s2
      (lookupStore xs (List.replicate j true) ((LooseWordList.words xs)[j]?.getD [])) c := by
    apply rename_executes_to CNFCloneEmitter.ClauseLookup.program lookupEmbedding g hc
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
    · intro i hi; fin_cases i <;> first | rfl | (exfalso; exact hi 0 rfl) | (exfalso; exact hi 1 rfl) | (exfalso; exact hi 2 rfl)
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 h3),?_⟩
  unfold rawLookupBound
  omega

 theorem listLookupOn_raw {k : ℕ} (φ : Fin 7 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (xs : BitString) (j : ℕ) (hs : s∘φ=lookupStore xs (List.replicate j true) []) :
    ∃ t, (listLookupOn φ).Executes g s (Function.update s (φ 2) ((LooseWordList.words xs)[j]?.getD [])) t ∧
      t≤rawLookupBound xs.length j := by
  obtain ⟨t,ht,hb⟩ := listLookup_raw g xs j
  refine ⟨t,?_,hb⟩
  apply rename_executes_to listLookup φ g ht hs
  · have he : (Function.update s (φ 2) ((LooseWordList.words xs)[j]?.getD []))∘φ =
        Function.update (s∘φ) 2 ((LooseWordList.words xs)[j]?.getD []) := by
      funext i; simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i; fin_cases i <;> rfl
  · intro i hi; exact Function.update_of_ne (hi 2).symm _ _
end HiddenCircuits.GraphReduction.Runtime
