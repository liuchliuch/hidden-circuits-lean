import HiddenCircuits.Approximation.FiniteChains.Decay

/-!
# Explicit uniform total-variation mixing

The theorem `CanonicalPaths.totalVariation_le_dyadic` turns actual bounded
paths and their edge traffic into a polynomial transition count. The proof
uses the finite-sum energy argument, not an assumed spectral gap.
-/
namespace HiddenCircuits.Approximation.FiniteChains
open scoped BigOperators
variable {α : Type*} [Fintype α]

/-- Total variation of two finite real-valued mass functions. -/
noncomputable def totalVariation (μ ν : α → ℝ) : ℝ :=
  (1:ℝ)/2 * ∑ x, |μ x-ν x|

namespace LazyChain
variable (P : LazyChain α)

noncomputable def pointMass (_P : LazyChain α) (s x : α) : ℝ := by classical exact if x=s then 1 else 0
noncomputable def uniform (_P : LazyChain α) : α → ℝ := fun _ => 1/(Fintype.card α : ℝ)
noncomputable def law (n : ℕ) (s : α) : α → ℝ := P.evolve n (P.pointMass s)

@[simp] theorem pointMass_sum (s : α) : ∑ x, P.pointMass s x = 1 := by
  classical
  simp [pointMass]

@[simp] theorem pointMass_sqNorm (s : α) : P.sqNorm (P.pointMass s) = 1 := by
  classical
  simp [sqNorm,pointMass,ite_pow]

theorem act_sub (f g : α → ℝ) : P.act (fun x => f x-g x) =
    fun x => P.act f x-P.act g x := by
  funext x
  simp [act,mul_sub,Finset.sum_sub_distrib]

theorem act_const (c : ℝ) : P.act (fun _ => c) = fun _ => c := by
  funext x
  simp [act,← Finset.sum_mul,P.row_sum]

theorem evolve_sub (n : ℕ) (f g : α → ℝ) :
    P.evolve n (fun x => f x-g x) = fun x => P.evolve n f x-P.evolve n g x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [evolve_succ,ih,act_sub]; rfl

theorem evolve_const (n : ℕ) (c : ℝ) : P.evolve n (fun _ => c) = fun _ => c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [evolve_succ,ih,act_const]

theorem evolve_nonneg (n : ℕ) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∀ x, 0 ≤ P.evolve n f x := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    intro x
    exact Finset.sum_nonneg fun y _ => mul_nonneg (P.nonneg x y) (ih y)

theorem law_nonneg (n : ℕ) (s x : α) : 0 ≤ P.law n s x := by
  apply P.evolve_nonneg
  intro y
  unfold pointMass
  split_ifs <;> positivity

@[simp] theorem law_sum (n : ℕ) (s : α) : ∑ x, P.law n s x = 1 := by
  rw [law,P.evolve_sum,P.pointMass_sum]

/-- The recursively defined law has the ordinary forward transition formula. -/
theorem law_succ (n : ℕ) (s x : α) :
    P.law (n+1) s x = ∑ y, P.law n s y * P.weight y x := by
  change (∑ y, P.weight x y * P.law n s y) = _
  apply Finset.sum_congr rfl
  intro y _
  rw [P.symmetric x y,mul_comm]

@[simp] theorem uniform_sum [Nonempty α] : ∑ x : α, P.uniform x = 1 := by
  have hn : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [uniform,hn]

theorem uniform_nonneg (x : α) : 0 ≤ P.uniform x := by unfold uniform; positivity

@[simp] theorem evolve_uniform (n : ℕ) : P.evolve n P.uniform = P.uniform :=
  P.evolve_const n _

theorem law_sub_uniform (n : ℕ) (s : α) :
    (fun x => P.law n s x-P.uniform x) =
      P.evolve n (fun x => P.pointMass s x-P.uniform x) := by
  rw [P.evolve_sub,P.evolve_uniform]
  rfl

theorem sqNorm_sub_const (f : α → ℝ) (c : ℝ) :
    P.sqNorm (fun x => f x-c) =
      P.sqNorm f - 2*c*(∑ x, f x) + Fintype.card α*c^2 := by
  unfold sqNorm
  calc
    _ = (∑ x, f x^2) - (∑ x, 2*c*f x) + ∑ _x : α, c^2 := by
      simp_rw [← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _; ring
    _ = _ := by simp [Finset.mul_sum]

theorem centered_point_sqNorm_le [Nonempty α] (s : α) :
    P.sqNorm (fun x => P.pointMass s x-P.uniform x) ≤ 1 := by
  have hn : (0:ℝ)<Fintype.card α := by exact_mod_cast Fintype.card_pos
  change P.sqNorm (fun x => P.pointMass s x-1/(Fintype.card α : ℝ)) ≤ 1
  rw [P.sqNorm_sub_const,P.pointMass_sqNorm,P.pointMass_sum]
  have he : 1-2*(1/(Fintype.card α : ℝ))*1 +
      Fintype.card α*(1/(Fintype.card α : ℝ))^2 = 1-1/(Fintype.card α : ℝ) := by
    field_simp
    <;> ring
  rw [he]
  have h : (0:ℝ)≤1/(Fintype.card α : ℝ) := by positivity
  linarith

/-- Finite Cauchy–Schwarz turns quadratic error into total variation. -/
theorem totalVariation_sq_le (μ ν : α → ℝ) :
    4*(totalVariation μ ν)^2 ≤ Fintype.card α * P.sqNorm (fun x => μ x-ν x) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset α)
    (fun _ => (1:ℝ)) (fun x => |μ x-ν x|)
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    mul_one,sq_abs] at h
  unfold totalVariation sqNorm
  nlinarith

end LazyChain

namespace CanonicalPaths
variable [Nonempty α] {P : LazyChain α} {K L Q : ℕ} (C : CanonicalPaths P K L Q)

/-- A polynomial transition budget in path length, traffic, inverse edge
probability, log state count and requested bits of accuracy. -/
def mixingSteps (B k : ℕ) : ℕ := 2*C.scale*(B+2*k)

/-- Canonical-path congestion implies uniform total-variation mixing.
The only analytic inputs are an actual lazy symmetric stochastic matrix;
all other hypotheses describe finite path data and their combinatorics. -/
theorem totalVariation_le_dyadic (B k : ℕ) (hcard : Fintype.card α ≤ 2^B) (s : α) :
    totalVariation (P.law (C.mixingSteps B k) s) P.uniform ≤ ((1:ℝ)/2)^k := by
  let f : α → ℝ := fun x => P.pointMass s x-P.uniform x
  have hf : ∑ x, f x = 0 := by
    dsimp [f]
    rw [Finset.sum_sub_distrib,P.pointMass_sum,P.uniform_sum,sub_self]
  have hnorm : P.sqNorm (P.evolve (C.mixingSteps B k) f) ≤ ((1:ℝ)/2)^(B+2*k) := by
    apply (C.dyadic_sqNorm_le (B+2*k) f hf).trans
    calc
      _ ≤ ((1:ℝ)/2)^(B+2*k)*1 :=
        mul_le_mul_of_nonneg_left (P.centered_point_sqNorm_le s) (by positivity)
      _ = _ := mul_one _
  have htv := P.totalVariation_sq_le (P.law (C.mixingSteps B k) s) P.uniform
  rw [P.law_sub_uniform] at htv
  have hcardR : (Fintype.card α : ℝ) ≤ (2:ℝ)^B := by exact_mod_cast hcard
  have hcancel : (2:ℝ)^B * ((1:ℝ)/2)^B = 1 := by
    rw [← mul_pow]
    norm_num
  have hpow : (Fintype.card α : ℝ) * ((1:ℝ)/2)^(B+2*k) ≤ (((1:ℝ)/2)^k)^2 := by
    calc
      _ ≤ (2:ℝ)^B*((1:ℝ)/2)^(B+2*k) :=
        mul_le_mul_of_nonneg_right hcardR (by positivity)
      _ = _ := by rw [pow_add,← mul_assoc,hcancel,one_mul,Nat.mul_comm 2 k,pow_mul]
  have hmul := mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg (Fintype.card α))
  have htarget : 0 ≤ ((1:ℝ)/2)^k := by positivity
  have hnonneg : 0 ≤ totalVariation (P.law (C.mixingSteps B k) s) P.uniform := by
    unfold totalVariation
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  dsimp [f] at hmul
  nlinarith [sq_nonneg (totalVariation (P.law (C.mixingSteps B k) s) P.uniform)]

end CanonicalPaths
end HiddenCircuits.Approximation.FiniteChains
