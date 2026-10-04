import HiddenCircuits.Approximation.CanonicalPaths.MountainSystem

/-! Fresh local event replacement proofs for overlapping mountain cells. -/
namespace HiddenCircuits.Approximation.CanonicalPaths.MountainSystem
open MountainIntervals
variable {E F : Type*} {H : ℕ} (A : Side E H) (B : Side F H)

def Separated : Prop := ∀ e f u v,A.height e u=B.height f v → A.height e u=0 ∨ A.height e u=H

theorem port_ext {p q : Port A B} (he : p.1.val.1=q.1.val.1) (hf : p.1.val.2=q.1.val.2)
    (hh : portHeight A B p=portHeight A B q) : p=q := by
  rcases p with ⟨⟨⟨e,f⟩,hp⟩,u⟩
  rcases q with ⟨⟨⟨e',f'⟩,hq⟩,v⟩
  dsimp only at he hf
  cases he
  cases hf
  apply Prod.ext
  · exact Subtype.ext rfl
  · exact height_injective hp hh

theorem right_straddles (hsep : Separated A B) (p : Port A B) (u : Bool)
    (hu : portHeight A B p=A.height p.1.val.1 u)
    (h₀ : portHeight A B p≠0) (hH : portHeight A B p≠H) :
    min (B.height p.1.val.2 false) (B.height p.1.val.2 true) < portHeight A B p ∧
    portHeight A B p < max (B.height p.1.val.2 false) (B.height p.1.val.2 true) := by
  apply other_strict p.1.property (portHeight_endpoint A B p)
  · intro h
    rcases hsep _ _ u false (hu.symm.trans h) with h|h
    · exact h₀ (hu.trans h)
    · exact hH (hu.trans h)
  · intro h
    rcases hsep _ _ u true (hu.symm.trans h) with h|h
    · exact h₀ (hu.trans h)
    · exact hH (hu.trans h)

/-- At an interior left-side vertex, its other incidence defines another valid cell. -/
theorem exists_left_replacement (hsep : Separated A B) (p : Port A B) (u : Bool)
    (hu : portHeight A B p=A.height p.1.val.1 u)
    (h₀ : portHeight A B p≠0) (hH : portHeight A B p≠H) :
    ∃ q : Port A B,q.1.val.1=(A.mate (p.1.val.1,u)).1 ∧ q.1.val.2=p.1.val.2 ∧
      portHeight A B q=portHeight A B p := by
  let t := A.mate (p.1.val.1,u)
  have ht : A.height t.1 t.2=portHeight A B p := (A.mate_height (p.1.val.1,u)).trans hu.symm
  have hb := right_straddles A B hsep p u hu h₀ hH
  have hnew : cellValid A B t.1 p.1.val.2 ∧
      (portHeight A B p=lower (A.height t.1 false) (A.height t.1 true) (B.height p.1.val.2 false) (B.height p.1.val.2 true) ∨
       portHeight A B p=upper (A.height t.1 false) (A.height t.1 true) (B.height p.1.val.2 false) (B.height p.1.val.2 true)) := by
    cases hv : t.2
    · have he : A.height t.1 false=portHeight A B p := by simpa only [hv] using ht
      have hn : portHeight A B p≠A.height t.1 true := by rw [← he]; exact A.nondegenerate t.1
      simpa only [cellValid,he] using replace_endpoint hn hb.1 hb.2
    · have he : A.height t.1 true=portHeight A B p := by simpa only [hv] using ht
      have hn : portHeight A B p≠A.height t.1 false := by rw [← he]; exact (A.nondegenerate t.1).symm
      simpa only [cellValid,he] using replace_endpoint_right hn hb.1 hb.2
  obtain ⟨v,hv⟩ := exists_height hnew.2
  exact ⟨(⟨(t.1,p.1.val.2),hnew.1⟩,v),rfl,rfl,hv⟩

def swapPort (p : Port A B) : Port B A :=
  (⟨(p.1.val.2,p.1.val.1),(overlap_comm _ _ _ _).mp p.1.property⟩,p.2)

theorem swapPort_height (p : Port A B) : portHeight B A (swapPort A B p)=portHeight A B p := by
  simp only [portHeight,swapPort,height,lower,upper,min_comm,max_comm]

theorem separated_swap (hsep : Separated A B) : Separated B A := by
  intro f e v u h
  rcases hsep e f u v h.symm with hh|hh
  · exact Or.inl (h.trans hh)
  · exact Or.inr (h.trans hh)

theorem exists_right_replacement (hsep : Separated A B) (p : Port A B) (u : Bool)
    (hu : portHeight A B p=B.height p.1.val.2 u)
    (h₀ : portHeight A B p≠0) (hH : portHeight A B p≠H) :
    ∃ q : Port A B,q.1.val.1=p.1.val.1 ∧ q.1.val.2=(B.mate (p.1.val.2,u)).1 ∧
      portHeight A B q=portHeight A B p := by
  have hs := swapPort_height A B p
  obtain ⟨q,hq₁,hq₂,hqH⟩ := exists_left_replacement B A (separated_swap A B hsep)
    (swapPort A B p) u (hs.trans hu) (fun h => h₀ (hs.symm.trans h)) (fun h => hH (hs.symm.trans h))
  exact ⟨swapPort B A q,hq₂,hq₁,(swapPort_height B A q).trans (hqH.trans hs)⟩

end HiddenCircuits.Approximation.CanonicalPaths.MountainSystem
