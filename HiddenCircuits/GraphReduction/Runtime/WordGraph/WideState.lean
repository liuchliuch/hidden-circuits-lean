import HiddenCircuits.GraphReduction.Runtime.WordGraph.GenericSolver

/-! Fresh reconstruction: empty-bank extension and actual finite-program
renaming. Wide query bodies retain their additional physical work ports. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.WideDriver
open Complexity OracleBlock BinaryArithmetic Polynomial
set_option maxHeartbeats 1000000

def extend (extra : ℕ) (s : Store 97) : Store (97+extra) := fun i =>
  if h : i.val<98 then s ⟨i.val,h⟩ else []
def embedding (extra : ℕ) : Fin 98 ↪ Fin (97+extra+1) where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun q : Fin (97+extra+1) => q.val) h)
noncomputable def lift (extra : ℕ) (B : OracleBlock 97) : OracleBlock (97+extra) := rename B (embedding extra)

theorem lift_executes (extra : ℕ) (B : OracleBlock 97) (g : BitString → ℕ) (s t : Store 97) (c : ℕ)
    (hc : B.Executes g s t c) : (lift extra B).Executes g (extend extra s) (extend extra t) c := by
  apply rename_executes_to B (embedding extra) g hc
  · funext i;simp [extend,embedding,Function.comp_def,i.isLt]
  · funext i;simp [extend,embedding,Function.comp_def,i.isLt]
  · intro i hi
    have hn : ¬i.val<98 := by intro h;exact hi ⟨i.val,h⟩ (Fin.ext rfl)
    simp [extend,hn]
lemma lift_queryFree (extra : ℕ) (B : OracleBlock 97) (h : B.QueryFree) : (lift extra B).QueryFree := rename_queryFree _ _ h

lemma extend_update (extra : ℕ) (s : Store 97) (i : Fin 98) (v : BitString) :
    extend extra (Function.update s i v)=Function.update (extend extra s) (embedding extra i) v := by
  funext q
  by_cases hq : q.val<98
  · simp [extend,Function.update_apply,embedding,Fin.ext_iff,hq]
  · have hn : ¬i.val=q.val := by intro he;have := i.isLt;omega
    simp [extend,Function.update_apply,embedding,Fin.ext_iff,hq,hn,Ne.symm hn]
@[simp] lemma extend_empty (extra : ℕ) : extend extra (fun _ => [])=(fun _ => []) := by
  funext q;simp [extend]
lemma extend_input (extra : ℕ) (bits : BitString) :
    extend extra (Function.update (fun _ : Fin 98 => []) 0 bits)=Function.update (fun _ => []) 0 bits := by
  rw [extend_update,extend_empty]
  rfl

def state (extra : ℕ) (w : WordInstance) (k t h l s : ℕ) (a : ℤ×ℤ) (answer num den : BitString) : Store (97+extra) :=
  extend extra (Driver.state w k t h l s a answer num den)
def bareState (w : WordInstance) (a b c : ℕ) : Store 135 := extend 38 (Driver.bareState w a b c)

lemma state_update_inner (w : WordInstance) (k t h l s l' : ℕ) (a : ℤ×ℤ) (answer num den : BitString) :
    Function.update (state 38 w k t h l s a answer num den) (8:Fin 136) (List.replicate l' true)=
      state 38 w k t h l' s a answer num den := by
  exact (extend_update 38 _ (8:Fin 98) _).symm.trans (congrArg (extend 38) (Driver.state_update_inner w k t h l s l' a answer num den))
lemma state_update_s (w : WordInstance) (k t h l s s' : ℕ) (a : ℤ×ℤ) (answer num den : BitString) :
    Function.update (state 38 w k t h l s a answer num den) (9:Fin 136) (List.replicate s' true)=
      state 38 w k t h l s' a answer num den := by
  exact (extend_update 38 _ (9:Fin 98) _).symm.trans (congrArg (extend 38) (Driver.state_update_s w k t h l s s' a answer num den))
lemma state_update_outer (w : WordInstance) (k t h l s k' : ℕ) (a : ℤ×ℤ) (answer num den : BitString) :
    Function.update (state 38 w k t h l s a answer num den) (5:Fin 136) (List.replicate k' true)=
      state 38 w k' t h l s a answer num den := by
  exact (extend_update 38 _ (5:Fin 98) _).symm.trans (congrArg (extend 38) (Driver.state_update_outer w k t h l s k' a answer num den))
lemma state_update_t (w : WordInstance) (k t h l s t' : ℕ) (a : ℤ×ℤ) (answer num den : BitString) :
    Function.update (state 38 w k t h l s a answer num den) (6:Fin 136) (List.replicate t' true)=
      state 38 w k t' h l s a answer num den := by
  exact (extend_update 38 _ (6:Fin 98) _).symm.trans (congrArg (extend 38) (Driver.state_update_t w k t h l s t' a answer num den))

noncomputable def rowPrepare : OracleBlock 135 := lift 38 Driver.rowPrepare
lemma rowPrepare_executes (g : BitString → ℕ) (w : WordInstance) (k t h : ℕ) (a : ℤ×ℤ) :
    rowPrepare.Executes g (state 38 w k t h 0 0 a [] [] [])
      (state 38 w k t (w.word.length+h) (2*w.particles*(w.word.length+h)+1) 0 a [] [] [])
      (5*w.word.length+(10*w.particles+9)*(w.word.length+h)+12) :=
  lift_executes 38 Driver.rowPrepare g _ _ _ (Driver.rowPrepare_executes g w k t h a)
lemma clearInnerIndex_executes (g : BitString → ℕ) (w : WordInstance) (k t h s : ℕ) (a : ℤ×ℤ) :
    (clear (9:Fin 136)).Executes g (state 38 w k t h 0 s a [] [] [])
      (state 38 w k t h 0 0 a [] [] []) (s+1) := by
  have hh := clear_executes g (9:Fin 136) (state 38 w k t h 0 s a [] [] [])
  change (clear (9:Fin 136)).Executes g _ (Function.update _ 9 (List.replicate 0 true)) ((List.replicate s true).length+1) at hh
  rw [state_update_s,List.length_replicate] at hh
  exact hh
end HiddenCircuits.GraphReduction.Runtime.WordGraph.WideDriver
