import HiddenCircuits.PerfectPartners
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Algebra.Group.Semiconj.Basic
import Mathlib.Algebra.Ring.Int.Parity

/-! The union of two fixed-point-free involutions
has two disjoint alternating orbits on each component. -/
namespace HiddenCircuits.Approximation.QuasimonotoneProof
open Equiv
variable {V : Type*} (p q : Equiv.Perm V)

def delta : Equiv.Perm V := q*p

theorem involution_inv (hp : Function.Involutive p) : p⁻¹=p := by
  apply Equiv.ext
  intro x
  apply p.injective
  simp only [Equiv.Perm.apply_inv_self,hp x]

theorem involution_zpow (hp : Function.Involutive p) (hq : Function.Involutive q)
    (k : ℤ) (x : V) : p (((delta p q)^k) x)=((delta p q)^(-k)) (p x) := by
  have hs : SemiconjBy p (delta p q) (delta p q)⁻¹ := by
    simp only [SemiconjBy,delta,mul_inv_rev,involution_inv p hp,involution_inv q hq,mul_assoc]
  have he := hs.zpow_right k
  have hv := congrArg (fun f : Equiv.Perm V => f x) he
  simpa only [Equiv.Perm.mul_apply,inv_zpow,← zpow_neg] using hv

theorem not_sameCycle_partner (hp : Function.Involutive p) (hq : Function.Involutive q)
    (hpFree : ∀x,p x≠x) (hqFree : ∀x,q x≠x) (x : V) :
    ¬(delta p q).SameCycle x (p x) := by
  rintro ⟨k,hk⟩
  obtain ⟨l,hl|hl⟩ := Int.even_or_odd' k
  · have he : p (((delta p q)^l) x)=((delta p q)^l) x := by
      rw [involution_zpow p q hp hq,← hk,hl]
      change (((delta p q)^(-l))*((delta p q)^(2*l))) x=((delta p q)^l) x
      rw [← zpow_add,show -l+2*l=l by omega]
    exact hpFree _ he
  · have he : p (((delta p q)^l) x)=((delta p q)^(l+1)) x := by
      rw [involution_zpow p q hp hq,← hk,hl]
      change (((delta p q)^(-l))*((delta p q)^(2*l+1))) x=((delta p q)^(l+1)) x
      rw [← zpow_add,show -l+(2*l+1)=l+1 by omega]
    have hd : delta p q (((delta p q)^l) x)=((delta p q)^(l+1)) x := by
      rw [zpow_add,zpow_one]
      simp only [Equiv.Perm.mul_apply]
      exact congrArg (fun f : Equiv.Perm V => f x) ((Commute.self_zpow (delta p q) l).eq)
    apply hqFree (((delta p q)^(l+1)) x)
    calc
      q (((delta p q)^(l+1)) x) = q (p (((delta p q)^l) x)) := congrArg q he.symm
      _ = delta p q (((delta p q)^l) x) := rfl
      _ = ((delta p q)^(l+1)) x := hd

def leftOrbit (base : V) : Set V := {x | (delta p q).SameCycle base x}
def rightOrbit (base : V) : Set V := p '' leftOrbit p q base

theorem p_left_to_right (base : V) {x : V} (hx : x∈leftOrbit p q base) :
    p x∈rightOrbit p q base := ⟨x,hx,rfl⟩

theorem p_right_to_left (hp : Function.Involutive p) (base : V) {x : V}
    (hx : x∈rightOrbit p q base) : p x∈leftOrbit p q base := by
  obtain ⟨y,hy,rfl⟩ := hx
  simpa only [hp y] using hy

theorem q_left_to_right (hp : Function.Involutive p) (hq : Function.Involutive q)
    (base : V) {x : V} (hx : x∈leftOrbit p q base) : q x∈rightOrbit p q base := by
  refine ⟨p (q x),?_,hp (q x)⟩
  have he : p (q x)=(delta p q)⁻¹ x := by
    simp only [delta,mul_inv_rev,involution_inv p hp,involution_inv q hq,Equiv.Perm.mul_apply]
  rw [he]
  exact hx.symm_apply_right

theorem q_right_to_left (hp : Function.Involutive p) (base : V) {x : V}
    (hx : x∈rightOrbit p q base) : q x∈leftOrbit p q base := by
  obtain ⟨y,hy,rfl⟩ := hx
  exact hy.apply_right

theorem orbits_disjoint (hp : Function.Involutive p) (hq : Function.Involutive q)
    (hpFree : ∀x,p x≠x) (hqFree : ∀x,q x≠x) (base : V) :
    Disjoint (leftOrbit p q base) (rightOrbit p q base) := by
  apply Set.disjoint_left.mpr
  intro x hx
  rintro ⟨y,hy,he⟩
  exact not_sameCycle_partner p q hp hq hpFree hqFree y (hy.symm.trans (he ▸ hx))

def partnerPerm {G : SimpleGraph V} (M : PerfectPartner G) : Equiv.Perm V :=
  ⟨M.val,M.val,M.property.1,M.property.1⟩
theorem partnerPerm_involutive {G : SimpleGraph V} (M : PerfectPartner G) : Function.Involutive (partnerPerm M) := M.property.1
theorem partnerPerm_free {G : SimpleGraph V} (M : PerfectPartner G) : ∀x,partnerPerm M x≠x :=
  fun x => (M.property.2 x).ne.symm

end HiddenCircuits.Approximation.QuasimonotoneProof
