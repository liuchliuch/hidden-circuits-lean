import HiddenCircuits.Approximation.CanonicalPaths.LocalRouteSupport
import HiddenCircuits.Approximation.CanonicalPaths.BlockRotation

/-! Actual source/target edges on an enumerated alternating cycle. -/
namespace HiddenCircuits.Approximation.CanonicalPaths
open LocalRoutes
variable {n : ℕ} (E : MonotoneEndpoints n)

structure CyclePresentation where
  rows : Equiv.Perm (Fin n)
  columns : Equiv.Perm (Fin n)
  sourceEdges : ∀i,Allowed E (rows i) (columns i)
  targetEdges : ∀i,Allowed E (rows (finRotate n i)) (columns i)

namespace CyclePresentation
variable {E} (D : CyclePresentation E)

def state (σ : Equiv.Perm (Fin n)) (hσ : ∀i,Allowed E (D.rows (σ i)) (D.columns i)) :
    State (fun col row => Allowed E row col) :=
  ⟨D.columns.symm.trans (σ.trans D.rows),fun col => by
    have h := hσ (D.columns.symm col)
    simpa only [Equiv.apply_symm_apply] using h⟩

@[simp] theorem state_apply (σ : Equiv.Perm (Fin n)) (hσ : ∀i,Allowed E (D.rows (σ i)) (D.columns i))
    (i : Fin n) : (D.state σ hσ).val (D.columns i)=D.rows (σ i) := by
  simp [state]

def source : State (fun col row => Allowed E row col) := D.state (Equiv.refl _) D.sourceEdges
def target : State (fun col row => Allowed E row col) := D.state (finRotate n) D.targetEdges

/-- A small cycle-index support remains small after restoring actual column labels. -/
theorem state_route (σ τ : Equiv.Perm (Fin n))
    (hσ : ∀i,Allowed E (D.rows (σ i)) (D.columns i))
    (hτ : ∀i,Allowed E (D.rows (τ i)) (D.columns i))
    (S : Finset (Fin n)) (hout : ∀i,i∉S → σ i=τ i) :
    ∃k ≤ S.card,Route (S.image D.columns) (D.state σ hσ) (D.state τ hτ) k := by
  have hh : ∀i,i∉S.image D.columns → (D.state σ hσ).val i=(D.state τ hτ).val i := by
    intro i hi
    let j := D.columns.symm i
    have hj : j∉S := by
      intro hj
      exact hi (Finset.mem_image.mpr ⟨j,hj,D.columns.apply_symm_apply i⟩)
    have he := hout j hj
    change D.rows (σ (D.columns.symm i))=D.rows (τ (D.columns.symm i))
    exact congrArg D.rows he
  obtain ⟨k,hk,hr⟩ := route_of_agree_outside (endpoint_ordered E) (D.state σ hσ) (D.state τ hτ)
    (S.image D.columns) hh
  exact ⟨k,hk.trans (Finset.card_image_le),hr⟩

end CyclePresentation
end HiddenCircuits.Approximation.CanonicalPaths
