import HiddenCircuits.Complexity.OracleIrrelevance
import HiddenCircuits.Complexity.SourceGrid.Program

/-! Disjoint source-grid and substituted-solver stacks. These embeddings are
actual instruction renamings and preserve every external frame. -/
namespace HiddenCircuits.Complexity.CanonicalSubstitution
open OracleBlock
variable {k : ℕ}

def baseEmbedding : Fin 43 ↪ Fin (k+44) where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun q : Fin (k+44) => q.val) h)
def workEmbedding : Fin (k+1) ↪ Fin (k+44) where
  toFun i := ⟨43+i.val,by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have hh := congrArg (fun q : Fin (k+44) => q.val) h
    change 43+i.val=43+j.val at hh
    omega

@[simp] lemma base_zero : baseEmbedding (k := k) 0=0 := rfl
lemma base_ne_work (i : Fin 43) (j : Fin (k+1)) : baseEmbedding i≠workEmbedding j := by
  intro h
  have hh := congrArg (fun q : Fin (k+44) => q.val) h
  change i.val=43+j.val at hh
  have hi := i.isLt
  omega

lemma port_cases (q : Fin (k+44)) :
    (∃ i : Fin 43, baseEmbedding i=q) ∨ (∃ j : Fin (k+1), workEmbedding j=q) := by
  by_cases h : q.val<43
  · exact Or.inl ⟨⟨q.val,h⟩,Fin.ext rfl⟩
  · exact Or.inr ⟨⟨q.val-43,by have:=q.isLt;omega⟩,Fin.ext (by dsimp [workEmbedding];omega)⟩

lemma wide_ext {s t : Store (k+43)}
    (hb : ∀ i, s (baseEmbedding i)=t (baseEmbedding i))
    (hw : ∀ i, s (workEmbedding i)=t (workEmbedding i)) : s=t := by
  funext q
  rcases port_cases q with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · exact hb i
  · exact hw i

def combined (s : Store 42) (w : Store k) : Store (k+43) := fun q =>
  if h : q.val<43 then s ⟨q.val,h⟩ else w ⟨q.val-43,by have:=q.isLt;omega⟩
def extend (s : Store 42) : Store (k+43) := combined s (fun _ => [])

@[simp] lemma combined_base (s : Store 42) (w : Store k) (i : Fin 43) :
    combined s w (baseEmbedding i)=s i := by simp [combined,baseEmbedding,i.isLt]
@[simp] lemma combined_work (s : Store 42) (w : Store k) (i : Fin (k+1)) :
    combined s w (workEmbedding i)=w i := by
  have hn : ¬43+i.val<43 := by omega
  simp [combined,workEmbedding,hn]
@[simp] lemma extend_base (s : Store 42) (i : Fin 43) : extend (k := k) s (baseEmbedding i)=s i := combined_base _ _ _
@[simp] lemma extend_work (s : Store 42) (i : Fin (k+1)) : extend (k := k) s (workEmbedding i)=[] := combined_work _ _ _

lemma update_base (s : Store 42) (w : Store k) (i : Fin 43) (x : BitString) :
    Function.update (combined s w) (baseEmbedding i) x=combined (Function.update s i x) w := by
  apply wide_ext
  · intro j;simp [Function.update_apply,baseEmbedding.injective.eq_iff]
  · intro j;simp only [Function.update_of_ne (base_ne_work i j).symm,combined_work]
lemma update_work (s : Store 42) (w : Store k) (i : Fin (k+1)) (x : BitString) :
    Function.update (combined s w) (workEmbedding i) x=combined s (Function.update w i x) := by
  apply wide_ext
  · intro j;simp only [Function.update_of_ne (base_ne_work j i),combined_base]
  · intro j;simp [Function.update_apply,workEmbedding.injective.eq_iff]

lemma combined_empty : combined (fun _ : Fin 43 => []) (fun _ : Fin (k+1) => [])=(fun _ => []) := by
  apply wide_ext <;> intro i <;> simp

lemma extend_initial (x : BitString) :
    extend (k := k) (Function.update (fun _ => []) 0 x)=Function.update (fun _ => []) 0 x := by
  change combined (Function.update (fun _ => []) (0 : Fin 43) x) (fun _ => [])=_
  rw [←update_base,combined_empty,base_zero]

noncomputable def liftBase (B : OracleBlock 42) : OracleBlock (k+43) := rename B baseEmbedding

theorem liftBase_executes (B : OracleBlock 42) (g : BitString → ℕ) (s t : Store 42) (c : ℕ)
    (hc : B.Executes g s t c) : (liftBase (k := k) B).Executes g (extend s) (extend t) c := by
  apply rename_executes_to B baseEmbedding g hc
  · funext i;exact extend_base _ _
  · funext i;exact extend_base _ _
  · intro q hq
    rcases port_cases q with ⟨i,rfl⟩ | ⟨i,rfl⟩
    · exact False.elim (hq i rfl)
    · simp

lemma liftBase_queryFree (B : OracleBlock 42) (hB : B.QueryFree) : (liftBase (k := k) B).QueryFree :=
  rename_queryFree _ _ hB

end HiddenCircuits.Complexity.CanonicalSubstitution
