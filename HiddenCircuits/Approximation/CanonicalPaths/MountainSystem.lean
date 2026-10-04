import HiddenCircuits.Approximation.CanonicalPaths.MountainIntervals
import HiddenCircuits.Approximation.CanonicalPaths.PortConnectivity

/-! Fresh local data for two polygonal sides and their actual overlap cells.
No path-existence or global-connectivity field is included. -/
namespace HiddenCircuits.Approximation.CanonicalPaths.MountainSystem
open MountainIntervals

structure Side (E : Type*) (H : ℕ) where
  height : E → Bool → ℕ
  nondegenerate : ∀e,height e false≠height e true
  upper_bound : ∀e b,height e b ≤ H
  mate : E × Bool → E × Bool
  mate_involutive : Function.Involutive mate
  mate_height : ∀p,height (mate p).1 (mate p).2=height p.1 p.2
  mate_fixed : ∀p,mate p=p ↔ height p.1 p.2=0 ∨ height p.1 p.2=H
  bottom : E × Bool
  top : E × Bool
  zero_iff : ∀p,height p.1 p.2=0 ↔ p=bottom
  top_iff : ∀p,height p.1 p.2=H ↔ p=top

namespace Side
variable {E : Type*} {H : ℕ} (A : Side E H)

theorem height_injective (e : E) : Function.Injective (A.height e) := by
  intro x y h
  cases x <;> cases y
  · rfl
  · exact False.elim (A.nondegenerate e h)
  · exact False.elim (A.nondegenerate e h.symm)
  · rfl

theorem mate_edge_eq_iff (p : E × Bool) : (A.mate p).1=p.1 ↔ A.mate p=p := by
  constructor
  · intro h
    apply Prod.ext h
    apply A.height_injective p.1
    have hh := A.mate_height p
    simpa only [h] using hh
  · intro h
    exact congrArg Prod.fst h

@[simp] theorem bottom_height : A.height A.bottom.1 A.bottom.2=0 := (A.zero_iff A.bottom).mpr rfl
@[simp] theorem top_height : A.height A.top.1 A.top.2=H := (A.top_iff A.top).mpr rfl

end Side

variable {E F : Type*} {H : ℕ} (A : Side E H) (B : Side F H)

def cellValid (e : E) (f : F) : Prop := Overlap (A.height e false) (A.height e true) (B.height f false) (B.height f true)

abbrev Cell := {p : E × F // cellValid A B p.1 p.2}
abbrev Port := Cell A B × Bool

def portHeight (p : Port A B) : ℕ :=
  height (A.height p.1.val.1 false) (A.height p.1.val.1 true)
    (B.height p.1.val.2 false) (B.height p.1.val.2 true) p.2

def crossCell (p : Port A B) : Port A B := (p.1,!p.2)

theorem crossCell_involutive : Function.Involutive (crossCell A B) := by
  rintro ⟨c,b⟩
  simp [crossCell]

theorem crossCell_free (p : Port A B) : crossCell A B p≠p := by
  intro h
  have hb := congrArg Prod.snd h
  cases hp : p.2 <;> simp [crossCell,hp] at hb

theorem portHeight_endpoint (p : Port A B) :
    portHeight A B p=lower (A.height p.1.val.1 false) (A.height p.1.val.1 true)
      (B.height p.1.val.2 false) (B.height p.1.val.2 true) ∨
    portHeight A B p=upper (A.height p.1.val.1 false) (A.height p.1.val.1 true)
      (B.height p.1.val.2 false) (B.height p.1.val.2 true) :=
  height_endpoint _ _ _ _ _

theorem portHeight_inside (p : Port A B) :
    min (A.height p.1.val.1 false) (A.height p.1.val.1 true) ≤ portHeight A B p ∧
    portHeight A B p ≤ max (A.height p.1.val.1 false) (A.height p.1.val.1 true) ∧
    min (B.height p.1.val.2 false) (B.height p.1.val.2 true) ≤ portHeight A B p ∧
    portHeight A B p ≤ max (B.height p.1.val.2 false) (B.height p.1.val.2 true) :=
  endpoint_inside p.1.property (portHeight_endpoint A B p)

theorem portHeight_origin (p : Port A B) :
    portHeight A B p=A.height p.1.val.1 false ∨ portHeight A B p=A.height p.1.val.1 true ∨
    portHeight A B p=B.height p.1.val.2 false ∨ portHeight A B p=B.height p.1.val.2 true :=
  endpoint_origin (portHeight_endpoint A B p)

end HiddenCircuits.Approximation.CanonicalPaths.MountainSystem
