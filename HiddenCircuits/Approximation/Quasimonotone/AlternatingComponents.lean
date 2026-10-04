import HiddenCircuits.Approximation.Quasimonotone.InvolutionOrbits
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
namespace HiddenCircuits.Approximation.QuasimonotoneProof
open Equiv
variable {V : Type*} (p q : Equiv.Perm V)
  (hp : Function.Involutive p) (hq : Function.Involutive q)
  (hpFree : ∀ x, p x≠x) (hqFree : ∀ x, q x≠x)
def pairGraph : SimpleGraph V where
  Adj x y := p x=y ∨ q x=y
  symm := by
    intro x y h
    rcases h with h|h
    · left; rw [← h]; exact hp x
    · right; rw [← h]; exact hq x
  loopless := ⟨fun x h => h.elim (hpFree x) (hqFree x)⟩
theorem p_reachable (x : V) : (pairGraph p q hp hq hpFree hqFree).Reachable x (p x) :=
  SimpleGraph.Adj.reachable (Or.inl rfl)
theorem q_reachable (x : V) : (pairGraph p q hp hq hpFree hqFree).Reachable x (q x) :=
  SimpleGraph.Adj.reachable (Or.inr rfl)
theorem delta_reachable (x : V) : (pairGraph p q hp hq hpFree hqFree).Reachable x (delta p q x) :=
  (p_reachable p q hp hq hpFree hqFree x).trans (q_reachable p q hp hq hpFree hqFree (p x))
theorem delta_iterate_reachable (x : V) (k : ℕ) :
    (pairGraph p q hp hq hpFree hqFree).Reachable x ((delta p q)^[k] x) := by
  induction k with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (delta_reachable p q hp hq hpFree hqFree _)
theorem orbit_reachable [Finite V] (base : V) {x : V} (hx : x∈leftOrbit p q base) :
    (pairGraph p q hp hq hpFree hqFree).Reachable base x := by
  obtain ⟨k,hk⟩ := hx.exists_nat_pow_eq
  have he : (delta p q)^[k] base=x := by simpa only [Equiv.Perm.coe_pow] using hk
  rw [← he]
  exact delta_iterate_reachable p q hp hq hpFree hqFree base k
theorem orbits_closed (base : V) {x y : V}
    (hx : x∈leftOrbit p q base ∪ rightOrbit p q base)
    (hxy : (pairGraph p q hp hq hpFree hqFree).Adj x y) :
    y∈leftOrbit p q base ∪ rightOrbit p q base := by
  rcases hx with hx|hx <;> rcases hxy with hxy|hxy
  · rw [← hxy]; exact Or.inr (p_left_to_right p q base hx)
  · rw [← hxy]; exact Or.inr (q_left_to_right p q hp hq base hx)
  · rw [← hxy]; exact Or.inl (p_right_to_left p q hp base hx)
  · rw [← hxy]; exact Or.inl (q_right_to_left p q hp base hx)
theorem reachable_iff_orbits [Finite V] (base x : V) :
    (pairGraph p q hp hq hpFree hqFree).Reachable base x ↔
      x∈leftOrbit p q base ∪ rightOrbit p q base := by
  constructor
  · intro hr
    have aux : ∀ {u v}, (pairGraph p q hp hq hpFree hqFree).Walk u v →
        u∈leftOrbit p q base ∪ rightOrbit p q base → v∈leftOrbit p q base ∪ rightOrbit p q base := by
      intro u v w
      induction w with
      | nil => exact id
      | cons huv path ih => exact fun hu => ih (orbits_closed p q hp hq hpFree hqFree base hu huv)
    exact hr.elim (fun w => aux w (Or.inl (Equiv.Perm.SameCycle.refl _ _)))
  · rintro (h|⟨y,hy,rfl⟩)
    · exact orbit_reachable p q hp hq hpFree hqFree base h
    · exact (orbit_reachable p q hp hq hpFree hqFree base hy).trans (p_reachable p q hp hq hpFree hqFree y)
def sourceCutEquiv (base : V) : leftOrbit p q base ≃ rightOrbit p q base where
  toFun x := ⟨p x.val,p_left_to_right p q base x.property⟩
  invFun y := ⟨p y.val,p_right_to_left p q hp base y.property⟩
  left_inv x := Subtype.ext (hp x.val)
  right_inv y := Subtype.ext (hp y.val)
def targetCutEquiv (base : V) : leftOrbit p q base ≃ rightOrbit p q base where
  toFun x := ⟨q x.val,q_left_to_right p q hp hq base x.property⟩
  invFun y := ⟨q y.val,q_right_to_left p q hp base y.property⟩
  left_inv x := Subtype.ext (hq x.val)
  right_inv y := Subtype.ext (hq y.val)
include hp in
theorem cut_balanced [Fintype V] (base : V) :
    Nat.card (leftOrbit p q base)=Nat.card (rightOrbit p q base) :=
  Nat.card_congr (sourceCutEquiv p q hp base)
end HiddenCircuits.Approximation.QuasimonotoneProof
