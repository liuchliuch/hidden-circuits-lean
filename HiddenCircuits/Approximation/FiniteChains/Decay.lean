import HiddenCircuits.Approximation.FiniteChains.Congestion

/-! Explicit geometric and dyadic decay from the proved path inequality. -/
namespace HiddenCircuits.Approximation.FiniteChains
open scoped BigOperators
variable {α : Type*} [Fintype α]

namespace LazyChain
variable (P : LazyChain α)

def evolve (P : LazyChain α) : ℕ → (α → ℝ) → (α → ℝ)
  | 0, f => f
  | n+1, f => P.act (evolve P n f)

@[simp] theorem evolve_zero (f : α → ℝ) : P.evolve 0 f = f := rfl
@[simp] theorem evolve_succ (n : ℕ) (f : α → ℝ) :
    P.evolve (n+1) f = P.act (P.evolve n f) := rfl

theorem evolve_sum (n : ℕ) (f : α → ℝ) : ∑ x, P.evolve n f x = ∑ x, f x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [evolve_succ,P.act_sum,ih]

theorem evolve_add (n m : ℕ) (f : α → ℝ) :
    P.evolve (n+m) f = P.evolve n (P.evolve m f) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.succ_add,evolve_succ,evolve_succ,ih]

end LazyChain

/-- An elementary geometric-series bound used to obtain a dyadic decay block. -/
theorem geometric_reciprocal_bound {d : ℝ} (hd : 0 ≤ d) (hd1 : d ≤ 1) (n : ℕ) :
    (1+(n:ℝ)*d)*(1-d)^n ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
    have hstep : (1+((n:ℝ)+1)*d)*(1-d) ≤ 1+(n:ℝ)*d := by
      nlinarith [mul_nonneg hn (sq_nonneg d)]
    calc
      _ = ((1+((n:ℝ)+1)*d)*(1-d))*(1-d)^n := by
        rw [Nat.cast_add,Nat.cast_one,pow_succ]; ring
      _ ≤ (1+(n:ℝ)*d)*(1-d)^n :=
        mul_le_mul_of_nonneg_right hstep (pow_nonneg (sub_nonneg.mpr hd1) _)
      _ ≤ 1 := ih

namespace CanonicalPaths
variable [Nonempty α] {P : LazyChain α} {K L Q : ℕ} (C : CanonicalPaths P K L Q)

noncomputable def factor : ℝ := 1 - 1/(2*(C.scale:ℝ))

theorem factor_nonneg : 0 ≤ C.factor := by
  have hc : (1:ℝ)≤C.scale := by exact_mod_cast (Nat.succ_le_iff.mpr C.scale_pos)
  unfold factor
  have h : (1:ℝ)/(2*C.scale) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  linarith

theorem factor_le_one : C.factor ≤ 1 := by
  unfold factor
  have h : (0:ℝ) ≤ 1/(2*(C.scale:ℝ)) := by positivity
  linarith

/-- One-step contraction, derived from the concrete path bound. -/
theorem contraction (f : α → ℝ) (hf : ∑ x, f x = 0) :
    P.sqNorm (P.act f) ≤ C.factor * P.sqNorm f := by
  have hc : (0:ℝ)<C.scale := by exact_mod_cast C.scale_pos
  have hp := C.poincare f hf
  have hd := P.sqNorm_act_le f
  have hdiv : P.sqNorm f/(2*C.scale) ≤ P.energy f/2 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*C.scale)).mpr
    nlinarith
  unfold factor
  have he : (1-1/(2*(C.scale:ℝ)))*P.sqNorm f =
      P.sqNorm f-P.sqNorm f/(2*C.scale) := by ring
  rw [he]
  linarith

theorem evolve_sqNorm_le (n : ℕ) (f : α → ℝ) (hf : ∑ x, f x = 0) :
    P.sqNorm (P.evolve n f) ≤ C.factor^n * P.sqNorm f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [LazyChain.evolve_succ]
    calc
      _ ≤ C.factor * P.sqNorm (P.evolve n f) :=
        C.contraction _ (by rw [P.evolve_sum,hf])
      _ ≤ C.factor * (C.factor^n * P.sqNorm f) :=
        mul_le_mul_of_nonneg_left ih C.factor_nonneg
      _ = _ := by rw [pow_succ]; ring

/-- Twice the integral relaxation scale is a verified halving block. -/
theorem block_factor_le : C.factor^(2*C.scale) ≤ (1:ℝ)/2 := by
  have hc : (0:ℝ)<C.scale := by exact_mod_cast C.scale_pos
  have hcle : (1:ℝ)≤C.scale := by exact_mod_cast (Nat.succ_le_iff.mpr C.scale_pos)
  have hd0 : (0:ℝ)≤1/(2*C.scale) := by positivity
  have hd1 : (1:ℝ)/(2*C.scale)≤1 :=
    (div_le_one (by positivity)).mpr (by linarith)
  have h := geometric_reciprocal_bound hd0 hd1 (2*C.scale)
  have he : 1+(↑(2*C.scale):ℝ)*(1/(2*C.scale)) = 2 := by
    push_cast
    field_simp
    <;> ring
  rw [he] at h
  change 2*C.factor^(2*C.scale) ≤ 1 at h
  linarith

theorem dyadic_factor_le (j : ℕ) :
    C.factor^(2*C.scale*j) ≤ ((1:ℝ)/2)^j := by
  rw [pow_mul]
  exact pow_le_pow_left₀ (pow_nonneg C.factor_nonneg _) C.block_factor_le j

/-- Polynomially many transitions give logarithmic-accuracy norm decay. -/
theorem dyadic_sqNorm_le (j : ℕ) (f : α → ℝ) (hf : ∑ x, f x = 0) :
    P.sqNorm (P.evolve (2*C.scale*j) f) ≤ ((1:ℝ)/2)^j * P.sqNorm f := by
  exact (C.evolve_sqNorm_le _ f hf).trans
    (mul_le_mul_of_nonneg_right (C.dyadic_factor_le j) (P.sqNorm_nonneg f))

end CanonicalPaths
end HiddenCircuits.Approximation.FiniteChains
