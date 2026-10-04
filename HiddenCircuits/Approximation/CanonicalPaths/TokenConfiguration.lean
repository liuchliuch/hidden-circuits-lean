import HiddenCircuits.Approximation.CanonicalPaths.CyclePresentation
import HiddenCircuits.Approximation.CanonicalPaths.TokenIndices

/-! Fresh actual primary and companion token matchings on a focus pair. -/
namespace HiddenCircuits.Approximation.CanonicalPaths.CyclePresentation
open LocalRoutes
variable {n : ℕ} {E : MonotoneEndpoints n} (D : CyclePresentation E)

def FocusOverlap (a b : Fin n) : Prop :=
  min (D.rows a) (D.rows (finRotate n a)) ≤ max (D.rows b) (D.rows (finRotate n b)) ∧
  min (D.rows b) (D.rows (finRotate n b)) ≤ max (D.rows a) (D.rows (finRotate n a))

def primaryCut (a b : Fin n) (hab : a < b) : Fin n :=
  rightCut b (by change a.val < b.val at hab; omega)
    (chooseSecond (decide (D.columns a ≤ D.columns b)) (D.rows b) (D.rows (finRotate n b)))

def companionCut (a b : Fin n) : Fin n :=
  leftCut a (chooseSecond (!(decide (D.columns a ≤ D.columns b))) (D.rows a) (D.rows (finRotate n a)))

theorem primaryCut_bounds (a b : Fin n) (hab : a < b) :
    b.val-1 ≤ (D.primaryCut a b hab).val ∧ (D.primaryCut a b hab).val ≤ b.val :=
  rightCut_bounds _ _ _

theorem primaryCut_ge (a b : Fin n) (hab : a < b) : a ≤ D.primaryCut a b hab :=
  left_le_rightCut a b hab _

variable [NeZero n]

theorem companionCut_bounds (a b : Fin n) (hab : a < b) :
    a.val ≤ (D.companionCut a b).val ∧ (D.companionCut a b).val ≤ a.val+1 :=
  leftCut_bounds a b hab _

theorem companionCut_le (a b : Fin n) (hab : a < b) : D.companionCut a b ≤ b :=
  leftCut_le_right a b hab _

theorem primary_chosen (a b : Fin n) (hab : a < b) :
    D.rows (finRotate n (D.primaryCut a b hab))=
      if D.columns a ≤ D.columns b then min (D.rows b) (D.rows (finRotate n b))
      else max (D.rows b) (D.rows (finRotate n b)) := by
  unfold primaryCut
  rw [rotate_rightCut]
  simp only [apply_ite]
  have h := chosen_extreme (decide (D.columns a ≤ D.columns b)) (D.rows b) (D.rows (finRotate n b))
  by_cases hc : D.columns a ≤ D.columns b <;> simpa [hc] using h

theorem companion_chosen (a b : Fin n) :
    D.rows (D.companionCut a b)=
      if D.columns a ≤ D.columns b then max (D.rows a) (D.rows (finRotate n a))
      else min (D.rows a) (D.rows (finRotate n a)) := by
  unfold companionCut leftCut
  simp only [apply_ite]
  have h := chosen_extreme (!(decide (D.columns a ≤ D.columns b))) (D.rows a) (D.rows (finRotate n a))
  by_cases hc : D.columns a ≤ D.columns b <;> simpa only [hc,decide_true,decide_false,Bool.not_true,Bool.not_false,↓reduceIte] using h

theorem focus_edges (a b : Fin n) (hab : a < b) (hov : D.FocusOverlap a b) :
    Allowed E (D.rows (finRotate n (D.primaryCut a b hab))) (D.columns a) ∧
    Allowed E (D.rows (D.companionCut a b)) (D.columns b) := by
  have h := dislocation_edges E (D.rows a) (D.rows (finRotate n a))
    (D.rows b) (D.rows (finRotate n b)) (D.columns a) (D.columns b)
    (D.sourceEdges a) (D.targetEdges a) (D.sourceEdges b) (D.targetEdges b) hov.1 hov.2
  rw [D.primary_chosen a b hab,D.companion_chosen a b]
  by_cases hc : D.columns a ≤ D.columns b
  · simpa only [if_pos hc] using h
  · simpa only [if_neg hc] using h

def primary (a b : Fin n) (hab : a < b) (hov : D.FocusOverlap a b) :
    State (fun col row => Allowed E row col) :=
  D.state (blockRotation a (D.primaryCut a b hab))
    (blockRotation_admissible a _ (D.primaryCut_ge a b hab)
      (fun i j => Allowed E (D.rows j) (D.columns i)) D.sourceEdges D.targetEdges (D.focus_edges a b hab hov).1)

def companion (a b : Fin n) (hab : a < b) (hov : D.FocusOverlap a b) :
    State (fun col row => Allowed E row col) :=
  D.state (Fin.cycleIcc (D.companionCut a b) b)
    (cycleIcc_admissible _ b (D.companionCut_le a b hab)
      (fun i j => Allowed E (D.rows j) (D.columns i)) D.sourceEdges D.targetEdges (D.focus_edges a b hab hov).2)

@[simp] theorem primary_apply (a b : Fin n) (hab : a < b) (hov : D.FocusOverlap a b) (i : Fin n) :
    (D.primary a b hab hov).val (D.columns i)=D.rows (blockRotation a (D.primaryCut a b hab) i) :=
  D.state_apply _ _ i

@[simp] theorem companion_apply (a b : Fin n) (hab : a < b) (hov : D.FocusOverlap a b) (i : Fin n) :
    (D.companion a b hab hov).val (D.columns i)=D.rows (Fin.cycleIcc (D.companionCut a b) b i) :=
  D.state_apply _ _ i

end HiddenCircuits.Approximation.CanonicalPaths.CyclePresentation
