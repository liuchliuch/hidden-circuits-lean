import HiddenCircuits.GraphReduction.Runtime.CliqueDirected

namespace HiddenCircuits.GraphReduction.Runtime.PrivateLayer
open Complexity OracleBlock
set_option maxHeartbeats 600000

def value (lower side : Bool) (layer : ℕ) : ℕ := layer+(if lower && side then 1 else 0)
def store (layer : ℕ) (side : Bool) (out : BitString) : Store 4 := fun i =>
  if i.val=0 then List.replicate layer true else if i.val=1 then [side] else if i.val=2 then out else []
noncomputable def addSide : OracleBlock 4 := seq (copyOn 1 3 4 (by decide) (by decide) (by decide))
  (branchPop 3 skip skip (push 2 true))
noncomputable def program (lower : Bool) : OracleBlock 4 :=
  if lower then seq (copyOn 0 2 4 (by decide) (by decide) (by decide)) addSide
  else copyOn 0 2 4 (by decide) (by decide) (by decide)

lemma addSide_executes (g : BitString→ℕ) (layer : ℕ) (side : Bool) :
    addSide.Executes g (store layer side (List.replicate layer true))
      (store layer side (List.replicate (layer+(if side then 1 else 0)) true)) 12 := by
  let start:=store layer side (List.replicate layer true)
  let a:=Function.update start (3:Fin 5) [side]
  have hc : (copyOn (1:Fin 5) 3 4 (by decide) (by decide) (by decide)).Executes g start a 7 := by
    simpa [a,start,store] using copyOn_executes g (1:Fin 5) 3 4 (by decide) (by decide) (by decide) start rfl
  have hu : Function.update a (3:Fin 5) []=start := by
    dsimp only [a]
    rw [Function.update_idem]
    exact Function.update_eq_self _ _
  have hs : (branchPop (3:Fin 5) skip skip (push 2 true)).Executes g a
      (store layer side (List.replicate (layer+(if side then 1 else 0)) true)) 3 := by
    cases side
    · apply branchPop_false _ _ _ _ g rfl
      rw [hu]
      simpa only [Bool.false_eq_true,ite_false,Nat.add_zero] using skip_executes g start
    · apply branchPop_true _ _ _ _ g rfl
      rw [hu]
      convert push_executes g (2:Fin 5) true start using 1
      funext i;fin_cases i <;> simp [start,store,List.replicate_succ]
  exact seq_executes _ _ g hc hs

theorem program_executes (g : BitString→ℕ) (lower side : Bool) (layer : ℕ) :
    ∃c,(program lower).Executes g (store layer side []) (store layer side (List.replicate (value lower side layer) true)) c ∧ c≤5*layer+16 := by
  have hc : (copyOn (0:Fin 5) 2 4 (by decide) (by decide) (by decide)).Executes g
      (store layer side []) (store layer side (List.replicate layer true)) (5*layer+2) := by
    convert copyOn_executes g (0:Fin 5) 2 4 (by decide) (by decide) (by decide) (store layer side []) rfl using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  cases lower
  · exact ⟨_,by simpa only [program,Bool.false_eq_true,ite_false,value,Bool.false_and,Nat.add_zero] using hc,by omega⟩
  · exact ⟨_,by simpa only [program,ite_true,value,Bool.true_and] using seq_executes _ _ g hc (addSide_executes g layer side),by omega⟩

lemma program_queryFree (lower : Bool) : (program lower).QueryFree := by
  cases lower
  · exact copyOn_queryFree _ _ _ _ _ _
  · exact seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
      (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (branchPop_queryFree _ _ _ _ skip_queryFree skip_queryFree (push_queryFree _ _)))
noncomputable def on {k : ℕ} (φ : Fin 5 ↪ Fin (k+1)) (lower : Bool) : OracleBlock k := rename (program lower) φ

theorem on_executes {k : ℕ} (φ : Fin 5 ↪ Fin (k+1)) (g : BitString→ℕ) (lower side : Bool) (layer : ℕ)
    (s : Store k) (hs:s∘φ=store layer side []) :
    ∃c,(on φ lower).Executes g s (Function.update s (φ 2) (List.replicate (value lower side layer) true)) c ∧ c≤5*layer+16 := by
  obtain ⟨c,hc,hb⟩:=program_executes g lower side layer
  refine ⟨c,?_,hb⟩
  apply rename_executes_to (program lower) φ g hc hs
  · have he:(Function.update s (φ 2) (List.replicate (value lower side layer) true))∘φ=
        Function.update (s∘φ) 2 (List.replicate (value lower side layer) true):=by funext i;simp[Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i;fin_cases i <;> rfl
  · intro i hi;exact Function.update_of_ne (hi 2).symm _ _
lemma on_queryFree {k : ℕ} (φ : Fin 5 ↪ Fin (k+1)) (lower : Bool) : (on φ lower).QueryFree := rename_queryFree _ _ (program_queryFree lower)
end HiddenCircuits.GraphReduction.Runtime.PrivateLayer
