import HiddenCircuits.Approximation.CanonicalPaths.MountainBoundaries
import Mathlib.Data.Fintype.Prod

/-! Fresh bounded discrete mountain climb from actual port involutions. -/
namespace HiddenCircuits.Approximation.CanonicalPaths.MountainSystem
attribute [local instance] Classical.propDecidable
variable {E F : Type*} {H : ℕ} (A : Side E H) (B : Side F H) (hsep : Separated A B)

noncomputable def eventGraph : SimpleGraph (Port A B) where
  Adj p q := p≠q ∧ (crossCell A B p=q ∨ vertexMate A B hsep p=q)
  symm := by
    intro p q h
    refine ⟨h.1.symm,?_⟩
    rcases h.2 with h|h
    · left
      rw [← h]
      exact crossCell_involutive A B p
    · right
      rw [← h]
      exact vertexMate_involutive A B hsep p
  loopless := ⟨fun p h => h.1 rfl⟩

theorem eventGraph_cross (p : Port A B) : (eventGraph A B hsep).Adj p (crossCell A B p) :=
  ⟨(crossCell_free A B p).symm,Or.inl rfl⟩

theorem eventGraph_vertex (p : Port A B) : vertexMate A B hsep p=p ∨
    (eventGraph A B hsep).Adj p (vertexMate A B hsep p) := by
  by_cases h : vertexMate A B hsep p=p
  · exact Or.inl h
  · exact Or.inr ⟨fun he => h he.symm,Or.inr rfl⟩

theorem vertexMate_extreme (p : Port A B) : vertexMate A B hsep p=p ↔
    p=bottomPort A B ∨ p=topPort A B := by
  rw [vertexMate_fixed,port_zero_iff,port_top_iff]

/-- An actual graph walk reaches the summit in fewer than twice the product of
side-edge counts. All side and pairing obligations have been proved explicitly. -/
theorem exists_bounded_climb [Fintype E] [Fintype F] :
    ∃ w : (eventGraph A B hsep).Walk (bottomPort A B) (topPort A B),
      w.length < 2*Fintype.card E*Fintype.card F := by
  classical
  obtain ⟨w,hw⟩ := boundary_ports_bounded_walk (eventGraph A B hsep)
    (crossCell A B) (vertexMate A B hsep) (bottomPort A B) (topPort A B)
    (crossCell_involutive A B) (vertexMate_involutive A B hsep)
    (crossCell_free A B) (vertexMate_extreme A B hsep)
    (eventGraph_cross A B hsep) (eventGraph_vertex A B hsep)
  have hc : Fintype.card (Cell A B) ≤ Fintype.card E*Fintype.card F := by
    simpa only [Fintype.card_prod] using
      Fintype.card_le_of_injective (fun c : Cell A B => c.val) Subtype.val_injective
  have hp : Fintype.card (Port A B) ≤ 2*Fintype.card E*Fintype.card F := by
    change Fintype.card (Cell A B × Bool) ≤ _
    rw [Fintype.card_prod,Fintype.card_bool]
    nlinarith
  exact ⟨w,hw.trans_le hp⟩

end HiddenCircuits.Approximation.CanonicalPaths.MountainSystem
