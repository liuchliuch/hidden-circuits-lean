import Mathlib.Tactic

/-! Fresh discrete interval geometry for the reconstructed mountain proof. -/
namespace HiddenCircuits.Approximation.CanonicalPaths.MountainIntervals

def lower (a b c d : ℕ) : ℕ := max (min a b) (min c d)
def upper (a b c d : ℕ) : ℕ := min (max a b) (max c d)
def Overlap (a b c d : ℕ) : Prop := lower a b c d < upper a b c d

theorem overlap_comm (a b c d : ℕ) : Overlap a b c d ↔ Overlap c d a b := by
  simp only [Overlap,lower,upper,max_comm,min_comm]

theorem endpoint_inside {a b c d h : ℕ} (hov : Overlap a b c d)
    (hh : h=lower a b c d ∨ h=upper a b c d) :
    min a b ≤ h ∧ h ≤ max a b ∧ min c d ≤ h ∧ h ≤ max c d := by
  unfold Overlap lower upper at *
  omega

theorem endpoint_origin {a b c d h : ℕ}
    (hh : h=lower a b c d ∨ h=upper a b c d) : h=a ∨ h=b ∨ h=c ∨ h=d := by
  unfold lower upper at hh
  omega

theorem other_strict {a b c d h : ℕ} (hov : Overlap a b c d)
    (hh : h=lower a b c d ∨ h=upper a b c d) (hc : h≠c) (hd : h≠d) :
    min c d < h ∧ h < max c d := by
  have hb := endpoint_inside hov hh
  omega

/-- A shared endpoint strictly inside the opposite edge can use either adjacent
nondegenerate edge. It remains an endpoint of the new nondegenerate overlap. -/
theorem replace_endpoint {h t c d : ℕ} (hne : h≠t)
    (hc : min c d < h) (hd : h < max c d) :
    Overlap h t c d ∧ (h=lower h t c d ∨ h=upper h t c d) := by
  unfold Overlap lower upper
  omega

theorem replace_endpoint_right {h t c d : ℕ} (hne : h≠t)
    (hc : min c d < h) (hd : h < max c d) :
    Overlap t h c d ∧ (h=lower t h c d ∨ h=upper t h c d) := by
  unfold Overlap lower upper
  omega

def height (a b c d : ℕ) (top : Bool) : ℕ := if top then upper a b c d else lower a b c d

theorem height_endpoint (a b c d : ℕ) (top : Bool) :
    height a b c d top=lower a b c d ∨ height a b c d top=upper a b c d := by
  cases top <;> simp [height]

theorem height_injective {a b c d : ℕ} (hov : Overlap a b c d) :
    Function.Injective (height a b c d) := by
  intro x y h
  cases x <;> cases y <;> simp_all [height,Overlap]

theorem exists_height {a b c d h : ℕ}
    (hh : h=lower a b c d ∨ h=upper a b c d) : ∃ top,height a b c d top=h := by
  rcases hh with h|h
  · exact ⟨false,h.symm⟩
  · exact ⟨true,h.symm⟩

end HiddenCircuits.Approximation.CanonicalPaths.MountainIntervals
