import HiddenCircuits.Approximation.CanonicalPaths.MountainPairing

/-! Fresh uniqueness proofs for the two extreme mountain ports. -/
namespace HiddenCircuits.Approximation.CanonicalPaths.MountainSystem
open MountainIntervals
namespace Side
variable {E : Type*} {H : ℕ} (A : Side E H)

theorem bottom_min : min (A.height A.bottom.1 false) (A.height A.bottom.1 true)=0 := by
  have hh := A.bottom_height
  cases hb : A.bottom.2 <;> simp only [hb] at hh <;> omega

theorem bottom_max_pos : 0 < max (A.height A.bottom.1 false) (A.height A.bottom.1 true) := by
  have hh := A.bottom_height
  have hn := A.nondegenerate A.bottom.1
  cases hb : A.bottom.2 <;> simp only [hb] at hh <;> omega

theorem top_max : max (A.height A.top.1 false) (A.height A.top.1 true)=H := by
  have hh := A.top_height
  have h₀ := A.upper_bound A.top.1 false
  have h₁ := A.upper_bound A.top.1 true
  cases hb : A.top.2 <;> simp only [hb] at hh <;> omega

theorem top_min_lt : min (A.height A.top.1 false) (A.height A.top.1 true) < H := by
  have hh := A.top_height
  have hn := A.nondegenerate A.top.1
  have h₀ := A.upper_bound A.top.1 false
  have h₁ := A.upper_bound A.top.1 true
  cases hb : A.top.2 <;> simp only [hb] at hh <;> omega
end Side

variable {E F : Type*} {H : ℕ} (A : Side E H) (B : Side F H)

theorem bottom_valid : cellValid A B A.bottom.1 B.bottom.1 := by
  change max (min _ _) (min _ _) < min (max _ _) (max _ _)
  rw [A.bottom_min,B.bottom_min,max_self]
  exact lt_min A.bottom_max_pos B.bottom_max_pos

theorem top_valid : cellValid A B A.top.1 B.top.1 := by
  change max (min _ _) (min _ _) < min (max _ _) (max _ _)
  rw [A.top_max,B.top_max,min_self]
  exact max_lt A.top_min_lt B.top_min_lt

def bottomPort : Port A B := (⟨(A.bottom.1,B.bottom.1),bottom_valid A B⟩,false)
def topPort : Port A B := (⟨(A.top.1,B.top.1),top_valid A B⟩,true)

@[simp] theorem bottomPort_height : portHeight A B (bottomPort A B)=0 := by
  simp only [portHeight,bottomPort,height,Bool.false_eq_true,↓reduceIte,lower,A.bottom_min,B.bottom_min,max_self]

@[simp] theorem topPort_height : portHeight A B (topPort A B)=H := by
  simp only [portHeight,topPort,height,↓reduceIte,upper,A.top_max,B.top_max,min_self]

theorem port_zero_iff (p : Port A B) : portHeight A B p=0 ↔ p=bottomPort A B := by
  constructor
  · intro h
    have hin := portHeight_inside A B p
    have hA : ∃u,A.height p.1.val.1 u=0 := by
      by_cases ha : A.height p.1.val.1 false=0
      · exact ⟨false,ha⟩
      · exact ⟨true,by omega⟩
    have hB : ∃v,B.height p.1.val.2 v=0 := by
      by_cases hb : B.height p.1.val.2 false=0
      · exact ⟨false,hb⟩
      · exact ⟨true,by omega⟩
    obtain ⟨u,hu⟩ := hA
    obtain ⟨v,hv⟩ := hB
    have he := congrArg Prod.fst ((A.zero_iff (p.1.val.1,u)).mp hu)
    have hf := congrArg Prod.fst ((B.zero_iff (p.1.val.2,v)).mp hv)
    exact port_ext A B he hf (h.trans (bottomPort_height A B).symm)
  · rintro rfl
    exact bottomPort_height A B

theorem port_top_iff (p : Port A B) : portHeight A B p=H ↔ p=topPort A B := by
  constructor
  · intro h
    have hin := portHeight_inside A B p
    have ha₀ := A.upper_bound p.1.val.1 false
    have ha₁ := A.upper_bound p.1.val.1 true
    have hb₀ := B.upper_bound p.1.val.2 false
    have hb₁ := B.upper_bound p.1.val.2 true
    have hA : ∃u,A.height p.1.val.1 u=H := by
      by_cases ha : A.height p.1.val.1 false=H
      · exact ⟨false,ha⟩
      · exact ⟨true,by omega⟩
    have hB : ∃v,B.height p.1.val.2 v=H := by
      by_cases hb : B.height p.1.val.2 false=H
      · exact ⟨false,hb⟩
      · exact ⟨true,by omega⟩
    obtain ⟨u,hu⟩ := hA
    obtain ⟨v,hv⟩ := hB
    have he := congrArg Prod.fst ((A.top_iff (p.1.val.1,u)).mp hu)
    have hf := congrArg Prod.fst ((B.top_iff (p.1.val.2,v)).mp hv)
    exact port_ext A B he hf (h.trans (topPort_height A B).symm)
  · rintro rfl
    exact topPort_height A B

end HiddenCircuits.Approximation.CanonicalPaths.MountainSystem
