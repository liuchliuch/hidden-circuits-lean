import HiddenCircuits.Complexity.Interpolation
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Intervals

namespace HiddenCircuits.Circuit
open scoped BigOperators

/-- The actual shared-power spectral nodes α_ab=4^a9^b. -/
def spectralNode (a b : ℕ) : ℕ := 4^a * 9^b

 theorem spectralNode_pos (a b : ℕ) : 0<spectralNode a b := by unfold spectralNode; positivity

/-- Unique prime factorization separates every pair of exponents, without a spectral assumption. -/
theorem spectralNode_injective : Function.Injective (fun p : ℕ×ℕ => spectralNode p.1 p.2) := by
  intro p q h
  have h2 := congrArg (fun n : ℕ => n.factorization 2) h
  have h3 := congrArg (fun n : ℕ => n.factorization 3) h
  simp only [spectralNode,Nat.factorization_mul (by positivity : (4:ℕ)^p.1≠0) (by positivity : (9:ℕ)^p.2≠0),
    Nat.factorization_mul (by positivity : (4:ℕ)^q.1≠0) (by positivity : (9:ℕ)^q.2≠0),
    Nat.factorization_pow,Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul] at h2 h3
  have h42 : (4:ℕ).factorization 2=2 := by decide +kernel
  have h43 : (4:ℕ).factorization 3=0 := by decide +kernel
  have h92 : (9:ℕ).factorization 2=0 := by decide +kernel
  have h93 : (9:ℕ).factorization 3=2 := by decide +kernel
  rw [h42,h92] at h2
  rw [h43,h93] at h3
  exact Prod.ext (by omega) (by omega)

/-- A concrete triangular enumeration of a,b≥0 with a+b≤g. -/
def SpectralIndex (g : ℕ) := (a : Fin (g+1)) × Fin (g-a.val+1)

instance spectralIndexFintype (g : ℕ) : Fintype (SpectralIndex g) :=
  inferInstanceAs (Fintype ((a : Fin (g+1)) × Fin (g-a.val+1)))
instance spectralIndexDecidableEq (g : ℕ) : DecidableEq (SpectralIndex g) :=
  inferInstanceAs (DecidableEq ((a : Fin (g+1)) × Fin (g-a.val+1)))

def spectralPair {g : ℕ} (x : SpectralIndex g) : ℕ×ℕ := (x.1.val,x.2.val)

 theorem spectralPair_bound {g : ℕ} (x : SpectralIndex g) : x.1.val+x.2.val≤g := by
  have h1 := x.1.isLt
  have h2 := x.2.isLt
  omega

 theorem spectralPair_injective (g : ℕ) : Function.Injective (@spectralPair g) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  have ha : a=c := Fin.ext (congrArg Prod.fst h)
  subst c
  have hb : b=d := Fin.ext (congrArg Prod.snd h)
  subst d
  rfl

 theorem spectralIndex_card_bound (g : ℕ) : Fintype.card (SpectralIndex g)≤(g+1)^2 := by
  let e : SpectralIndex g → Fin (g+1) × Fin (g+1) :=
    fun x => (x.1,⟨x.2.val,by have h := spectralPair_bound x; omega⟩)
  have he : Function.Injective e := by
    intro x y h
    apply spectralPair_injective g
    exact congrArg (fun z : Fin (g+1)×Fin (g+1) => (z.1.val,z.2.val)) h
  have h := Fintype.card_le_of_injective e he
  simpa only [Fintype.card_prod,Fintype.card_fin,pow_two] using h

/-- Every spectral node has a linear-bit exponential envelope. -/
theorem spectralNode_bound {g : ℕ} (x : SpectralIndex g) :
    spectralNode x.1.val x.2.val ≤ 16^g := by
  unfold spectralNode
  calc
    4^x.1.val * 9^x.2.val ≤ 16^x.1.val * 16^x.2.val :=
      Nat.mul_le_mul (Nat.pow_le_pow_left (by decide) _) (Nat.pow_le_pow_left (by decide) _)
    _ = 16^(x.1.val+x.2.val) := (pow_add ..).symm
    _ ≤ 16^g := Nat.pow_le_pow_right (by decide) (spectralPair_bound x)


/-- The exact triangular number of distinct spectral nodes. -/
theorem spectralIndex_card_twice (g : ℕ) :
    Fintype.card (SpectralIndex g)*2=(g+1)*(g+2) := by
  change Fintype.card ((a : Fin (g+1)) × Fin (g-a.val+1))*2=_
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  have hr : (∑ a : Fin (g+1), (g - a.val + 1)) = ∑ a : Fin (g+1), (a.val + 1) := by
    let e : Fin (g+1) ≃ Fin (g+1) :=
      ⟨Fin.rev,Fin.rev,Fin.rev_rev,Fin.rev_rev⟩
    have h := e.sum_comp (fun a : Fin (g+1) => a.val+1)
    simpa [e,Fin.val_rev] using h
  rw [hr,Fin.sum_univ_eq_sum_range (fun a : ℕ => a+1)]
  have hs := Finset.sum_range_id_mul_two (g+1)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one]
  simp only [Nat.add_sub_cancel] at hs
  nlinarith

 theorem spectralIndex_card (g : ℕ) : Fintype.card (SpectralIndex g)=(g+1)*(g+2)/2 := by
  rw [← spectralIndex_card_twice,Nat.mul_div_cancel]
  decide

end HiddenCircuits.Circuit
