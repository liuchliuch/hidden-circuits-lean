import HiddenCircuits.Approximation.CanonicalPaths.MountainClimbing

/-! Actual local-move bounds transport through the mountain incidence graph. -/
namespace HiddenCircuits.Approximation.CanonicalPaths.MountainSystem
variable {E F : Type*} {H : ℕ} (A : Side E H) (B : Side F H) (hsep : Separated A B)

theorem event_step_bounds (fa : E → ℕ) (fb : F → ℕ)
    (ha : ∀p,fa (A.mate p).1 ≤ fa p.1+1 ∧ fa p.1 ≤ fa (A.mate p).1+1)
    (hb : ∀p,fb (B.mate p).1 ≤ fb p.1+1 ∧ fb p.1 ≤ fb (B.mate p).1+1)
    {p q : Port A B} (h : (eventGraph A B hsep).Adj p q) :
    fa p.1.val.1 ≤ fa q.1.val.1+1 ∧ fa q.1.val.1 ≤ fa p.1.val.1+1 ∧
    fb p.1.val.2 ≤ fb q.1.val.2+1 ∧ fb q.1.val.2 ≤ fb p.1.val.2+1 := by
  rcases h.2 with h|h
  · rw [← h]
    simp [crossCell]
  · have hi := vertexMate_incidence A B hsep p
    rw [h] at hi
    rcases hi with hi|hi
    · obtain ⟨u,_,he,hf,_⟩ := hi
      rw [he,hf]
      have hh := ha (p.1.val.1,u)
      exact ⟨hh.2,hh.1,Nat.le_succ _,Nat.le_succ _⟩
    · obtain ⟨u,_,he,hf,_⟩ := hi
      rw [he,hf]
      have hh := hb (p.1.val.2,u)
      exact ⟨Nat.le_succ _,Nat.le_succ _,hh.2,hh.1⟩

end HiddenCircuits.Approximation.CanonicalPaths.MountainSystem
