import HiddenCircuits.DH.Runtime.BagStateModel

/-! Cached numeric table execution for the exhaustive pruning trace. Bag
expressions appear only in the proved refinement relation, never as input
certificates or numeric table entries. -/
namespace HiddenCircuits.DH.Runtime.NumericStateModel
open PruningModel

structure State (n : ℕ) where
  alive : Vector Bool n
  sizes : Vector ℕ n
  rows : Vector (List ℕ) n

def initial (n : ℕ) : State n :=
  ⟨Vector.replicate n true,Vector.replicate n 1,Vector.replicate n (CoefficientModel.leafRow n)⟩

def update {n : ℕ} (s : State n) (a : Action n) : State n :=
  ⟨remove s.alive a,s.sizes.set a.keep.val (s.sizes[a.keep.val]+s.sizes[a.removed.val]),
    s.rows.set a.keep.val (CoefficientModel.mergeRow n a.kind s.sizes[a.keep.val] s.sizes[a.removed.val]
      s.rows[a.keep.val] s.rows[a.removed.val])⟩

def execute {n : ℕ} : List (Action n)→State n→State n
  | [],s => s
  | a::as,s => execute as (update s a)

def Represents {n : ℕ} (numeric : State n) (bags : ModuleExecution.Store n) : Prop :=
  numeric.alive=bags.alive ∧
    (∀v : Fin n, numeric.sizes[v.val]=bags.bags[v.val].size) ∧
    (∀v : Fin n, CoefficientModel.Represents numeric.rows[v.val] bags.bags[v.val])

lemma initial_represents (n : ℕ) : Represents (initial n) (ModuleExecution.initial n) := by
  refine ⟨rfl,?_,?_⟩
  · intro v;simp [initial,ModuleExecution.initial,BagExpr.size]
  · intro v
    simpa only [initial,ModuleExecution.initial,Vector.getElem_replicate] using
      CoefficientModel.leafRow_represents n (by have h:=v.isLt;omega)

lemma update_represents_of_size {n : ℕ} {bags : ModuleExecution.Store n}
    (s : State n) (hs : Represents s bags) (a : Action n) (hne : a.keep≠a.removed)
    (hsize : bags.bags[a.keep.val].size+bags.bags[a.removed.val].size≤n) :
    Represents (update s a) (applyBag bags a) := by
  refine ⟨?_,?_,?_⟩
  · change remove s.alive a=(applyBag bags a).alive
    rw [hs.1,applyBag_alive bags a hne]
  · intro v
    by_cases hv : v=a.keep
    · subst v
      simp only [update,Vector.getElem_set_self,applyBag_kept,CoefficientModel.mergeBag_size]
      rw [hs.2.1,hs.2.1]
    · have hval : a.keep.val≠v.val := fun he=>hv (Fin.ext he).symm
      simp only [update]
      simp only [Vector.getElem_set,if_neg hval]
      rw [applyBag_other bags a v hv]
      exact hs.2.1 v
  · intro v
    by_cases hv : v=a.keep
    · subst v
      simp only [update,Vector.getElem_set_self,applyBag_kept]
      rw [hs.2.1,hs.2.1]
      exact CoefficientModel.mergeRow_represents n a.kind _ _ _ _ (hs.2.2 a.keep) (hs.2.2 a.removed) hsize
    · have hval : a.keep.val≠v.val := fun he=>hv (Fin.ext he).symm
      simp only [update]
      simp only [Vector.getElem_set,if_neg hval]
      rw [applyBag_other bags a v hv]
      exact hs.2.2 v

lemma update_represents {n : ℕ} {G : SimpleGraph (Fin n)} {bags : ModuleExecution.Store n}
    (I : ModuleExecution.Interpretation G bags) (s : State n) (hs : Represents s bags)
    (a : Action n) (ha : Valid G bags.alive a) : Represents (update s a) (applyBag bags a) := by
  have I' := applyBag_interpretation I a ha
  have hkeep : (applyBag bags a).alive[a.keep.val]=true := by
    rw [applyBag_alive bags a ha.2.2.1,remove_alive]
    exact ⟨ha.1,ha.2.2.1⟩
  have hsize : bags.bags[a.keep.val].size+bags.bags[a.removed.val].size≤n := by
    have h := interpretation_bag_size I' a.keep hkeep
    rw [applyBag_kept,CoefficientModel.mergeBag_size] at h
    exact h
  exact update_represents_of_size s hs a ha.2.2.1 hsize

/-- The full numeric execution has the exact genuine bag coefficients after
every checked pruning action, including inactive frozen table slots. -/
theorem trace_represents {n : ℕ} {G : SimpleGraph (Fin n)} {alive final : Vector Bool n}
    {as : List (Action n)} (h : Trace G alive as final)
    (bags : ModuleExecution.Store n) (hb : bags.alive=alive) (I : ModuleExecution.Interpretation G bags)
    (s : State n) (hs : Represents s bags) :
    Represents (execute as s) (executeActions as bags) := by
  induction h generalizing bags s with
  | nil alive => exact hs
  | @cons alive final a as valid rest ih =>
    have ha : Valid G bags.alive a := hb ▸ valid
    have hb' : (applyBag bags a).alive=remove alive a := (applyBag_alive bags a ha.2.2.1).trans
      (congrArg (fun x=>remove x a) hb)
    exact ih (applyBag bags a) hb' (applyBag_interpretation I a ha) (update s a) (update_represents I s hs a ha)

lemma update_row_lengths {n : ℕ} (s : State n) (a : Action n)
    (h : ∀v : Fin n, (s.rows[v.val]).length=n+1) :
    ∀v : Fin n, ((update s a).rows[v.val]).length=n+1 := by
  intro v
  by_cases hv : v=a.keep
  · subst v;simp [update]
  · have hval : a.keep.val≠v.val := fun he=>hv (Fin.ext he).symm
    simpa [update,hval] using h v

lemma execute_row_lengths {n : ℕ} (as : List (Action n)) (s : State n)
    (h : ∀v : Fin n, (s.rows[v.val]).length=n+1) :
    ∀v : Fin n, ((execute as s).rows[v.val]).length=n+1 := by
  induction as generalizing s with
  | nil => exact h
  | cons a as ih => exact ih (update s a) (update_row_lengths s a h)

end HiddenCircuits.DH.Runtime.NumericStateModel
