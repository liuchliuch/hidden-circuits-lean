import HiddenCircuits.DH.Runtime.FinalModel
import HiddenCircuits.DH.Runtime.BagVolume
import HiddenCircuits.DH.Runtime.PairSearchOrder

/-! A total bounded-iteration extension on arbitrary Boolean matrices. The
semantic promise is used only for the final perfect-matching equality. -/
namespace HiddenCircuits.DH.Runtime.NumericStateModel
open PruningModel PairCheck

/-- Graph-independent witnesses control every cached count on all inputs. -/
def Safe {n : ℕ} (s : State n) : Prop :=
  ∃bags : ModuleExecution.Store n, Represents s bags ∧ volume bags=n ∧
    (∀v : Fin n, bags.bags[v.val].size≤n) ∧ (∀v : Fin n, (s.rows[v.val]).length=n+1)

lemma initial_safe (n : ℕ) : Safe (initial n) := by
  refine ⟨ModuleExecution.initial n,initial_represents n,initial_volume n,?_,?_⟩
  · intro v
    simp only [ModuleExecution.initial,Vector.getElem_replicate,BagExpr.size]
    have h:=v.isLt
    omega
  · intro v;simp [initial]

lemma update_safe {n : ℕ} (s : State n) (h : Safe s) (a : Action n)
    (hu : s.alive[a.keep.val]=true) (hv : s.alive[a.removed.val]=true) (hne : a.keep≠a.removed) :
    Safe (update s a) := by
  obtain ⟨bags,hr,hvol,hsize,hlen⟩ := h
  have hu' : bags.alive[a.keep.val]=true := hr.1 ▸ hu
  have hv' : bags.alive[a.removed.val]=true := hr.1 ▸ hv
  have hvol' : volume (applyBag bags a)=n := (applyBag_volume bags a hu' hv' hne).trans hvol
  have hb := (applyBag_bounded bags a hu' hv' hne hvol.le hsize).2
  have hsum : bags.bags[a.keep.val].size+bags.bags[a.removed.val].size≤n := by
    have hh := hb a.keep
    rw [applyBag_kept,CoefficientModel.mergeBag_size] at hh
    exact hh
  exact ⟨applyBag bags a,update_represents_of_size s hr a hne hsum,hvol',hb,update_row_lengths s a hlen⟩

def rawStep {n : ℕ} (G : MatrixData n) (s : State n) : State n :=
  match PairSearch.find G s.alive with
  | none => s
  | some a => update s a

def rawRun {n : ℕ} (G : MatrixData n) : ℕ→State n→State n
  | 0,s => s
  | fuel+1,s => rawRun G fuel (rawStep G s)

lemma rawStep_safe {n : ℕ} (G : MatrixData n) (s : State n) (h : Safe s) : Safe (rawStep G s) := by
  cases he : PairSearch.find G s.alive with
  | none => simpa only [rawStep,he] using h
  | some a =>
    obtain ⟨hu,hv,hne⟩ := PairSearch.find_live G s.alive he
    simpa only [rawStep,he] using update_safe s h a hu hv hne

lemma rawRun_safe {n : ℕ} (G : MatrixData n) (fuel : ℕ) (s : State n) (h : Safe s) : Safe (rawRun G fuel s) := by
  induction fuel generalizing s with
  | zero => exact h
  | succ fuel ih => exact ih (rawStep G s) (rawStep_safe G s h)

lemma Safe.size_bound {n : ℕ} {s : State n} (h : Safe s) (v : Fin n) : s.sizes[v.val]≤n := by
  obtain ⟨bags,hr,hv,hb,hl⟩ := h
  rw [hr.2.1]
  exact hb v

lemma Safe.coefficient_bound {n : ℕ} {s : State n} (h : Safe s) (v : Fin n) (k : ℕ) :
    CoefficientModel.read s.rows[v.val] k≤2^((n+1)^2) := by
  obtain ⟨bags,hr,hv,hb,hl⟩ := h
  exact CoefficientModel.row_bound _ _ n (hr.2.2 v) (hb v) k

lemma Safe.row_lengths {n : ℕ} {s : State n} (h : Safe s) : ∀v : Fin n, (s.rows[v.val]).length=n+1 := by
  obtain ⟨bags,hr,hv,hb,hl⟩ := h
  exact hl

lemma rawRun_ofGraph {n : ℕ} (G : Complexity.MatrixGraph n) (fuel : ℕ) (s : State n) :
    rawRun (MatrixData.ofGraph G) fuel s=
      execute (PruningModel.run G.graph fuel s.alive).actions s := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    simp only [rawRun,rawStep,PairSearch.find_ofGraph]
    cases he : PruningModel.find G.graph s.alive with
    | none =>
      simp only []
      rw [ih]
      cases fuel with
      | zero => simp only [PruningModel.run,he,execute]
      | succ f => simp only [PruningModel.run,he,execute]
    | some a =>
      simp only []
      rw [ih]
      simp only [PruningModel.run,he,execute,update]

/-- The matrix-level total extension runs a fixed input-size number of rounds
and computes PM on every distance-hereditary graph in the promised domain. -/
theorem raw_count_correct {n : ℕ} (G : Complexity.MatrixGraph n)
    (hG : DistanceHereditaryGraph G.graph) :
    result (rawRun (MatrixData.ofGraph G) n (initial n))=perfectMatchingCount G.graph := by
  rw [rawRun_ofGraph]
  exact count_correct G.graph hG

end HiddenCircuits.DH.Runtime.NumericStateModel
