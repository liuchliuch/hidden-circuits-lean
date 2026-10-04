import HiddenCircuits.GraphReduction.Runtime.DirectedCompare
import HiddenCircuits.GraphReduction.Runtime.DirectedBoolean

/-! A complete finite bit program for the local directed cut/probe predicate. -/
namespace HiddenCircuits.GraphReduction.Runtime
open Complexity Complexity.OracleBlock

def dirWork : List (Fin 41) := [19,20,21,22,23,24,25,26,27,28,29,30,31]
noncomputable def directedPredicate : OracleBlock 40 :=
  seq dirPrepare (seq dirCompare (seq dirBoolean (clearList dirWork)))

theorem directedPredicate_executes (g : BitString → ℕ) (x y : VertexRecord) :
    ∃ c, directedPredicate.Executes g (dirStore x y [] [] (fun _ => []) [])
      (dirStore x y [] [] (fun _ => []) [directedRecordAdj x y]) c ∧ c≤200*dirSize x y+800 := by
  have hp := dirPrepare_executes g x y
  obtain ⟨c,hc,hcb⟩ := dirCompare_executes g x y
  have hb := dirBoolean_executes g x y
  obtain ⟨t,ht,htb⟩ := clearList_executes g dirWork (dirState x y 11 [directedRecordAdj x y])
    (dirSize x y) (dirState_length x y 11 [directedRecordAdj x y] (by simp))
  have he : eraseStore dirWork (dirState x y 11 [directedRecordAdj x y]) =
      dirStore x y [] [] (fun _ => []) [directedRecordAdj x y] := by
    funext i; fin_cases i <;> simp [eraseStore,dirWork,dirState,dirStore]
  rw [he] at ht
  refine ⟨_,seq_executes _ _ g hp (seq_executes _ _ g hc (seq_executes _ _ g hb ht)),?_⟩
  have hcoord := dir_coordinates_bound x y
  simp only [dirWork,List.length_cons,List.length_nil] at htb
  omega

lemma directedPredicate_queryFree : directedPredicate.QueryFree :=
  seq_queryFree _ _ dirPrepare_queryFree (seq_queryFree _ _ dirCompare_queryFree
    (seq_queryFree _ _ dirBoolean_queryFree (clearList_queryFree _)))

noncomputable def directedPredicateOn {k : ℕ} (φ : Fin 41 ↪ Fin (k+1)) : OracleBlock k := rename directedPredicate φ

theorem directedPredicateOn_executes {k : ℕ} (φ : Fin 41 ↪ Fin (k+1)) (g : BitString → ℕ)
    (x y : VertexRecord) (s : Store k) (hs : s∘φ=dirStore x y [] [] (fun _ => []) []) :
    ∃ c, (directedPredicateOn φ).Executes g s (Function.update s (φ 18) [directedRecordAdj x y]) c ∧
      c≤200*dirSize x y+800 := by
  obtain ⟨c,hc,hb⟩ := directedPredicate_executes g x y
  refine ⟨c,?_,hb⟩
  apply rename_executes_to directedPredicate φ g hc hs
  · have he : (Function.update s (φ 18) [directedRecordAdj x y])∘φ =
        Function.update (s∘φ) 18 [directedRecordAdj x y] := by
      funext i; simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i; fin_cases i <;> rfl
  · intro i hi; exact Function.update_of_ne (hi 18).symm _ _
lemma directedPredicateOn_queryFree {k : ℕ} (φ : Fin 41 ↪ Fin (k+1)) : (directedPredicateOn φ).QueryFree :=
  rename_queryFree _ _ directedPredicate_queryFree

end HiddenCircuits.GraphReduction.Runtime
