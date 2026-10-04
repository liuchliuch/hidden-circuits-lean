import HiddenCircuits.Approximation.FiniteChains.Energy

/-! Canonical-path traffic controls the quadratic norm of centered functions. -/
namespace HiddenCircuits.Approximation.FiniteChains
open scoped BigOperators
variable {α : Type*} [Fintype α]

noncomputable def traffic (paths : ∀ x y : α, Path x y) (a b : α) : ℕ :=
  ∑ x, ∑ y, (paths x y).edgeCount a b

/-- The finite routes and their independently proved combinatorial bounds.
There is deliberately no mixing, gap, or Poincaré hypothesis here. -/
structure CanonicalPaths (P : LazyChain α) (K L Q : ℕ) where
  path : ∀ x y : α, Path x y
  length_le : ∀ x y, (path x y).length ≤ L
  traffic_le : ∀ a b, traffic path a b ≤ K * Fintype.card α
  Q_pos : 0 < Q
  transition_lower : ∀ x y (i : Fin (path x y).length),
    (1:ℝ)/Q ≤ P.weight ((path x y).vertex i.castSucc) ((path x y).vertex i.succ)

/-- Collecting all path edges counts multiplicities exactly. -/
theorem sum_edgeSum_eq_traffic (paths : ∀ x y : α, Path x y) (g : α → α → ℝ) :
    (∑ x, ∑ y, (paths x y).edgeSum g) =
      ∑ a, ∑ b, (traffic paths a b : ℝ) * g a b := by
  simp_rw [Path.edgeSum_eq_count]
  have hswap (h : α → α → α → α → ℝ) :
      (∑ x, ∑ y, ∑ a, ∑ b, h x y a b) = ∑ a, ∑ b, ∑ x, ∑ y, h x y a b := by
    calc
      _ = ∑ x, ∑ a, ∑ b, ∑ y, h x y a b := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]
  rw [hswap]
  simp only [traffic,Nat.cast_sum,Finset.sum_mul]

namespace CanonicalPaths
variable {P : LazyChain α} {K L Q : ℕ} (C : CanonicalPaths P K L Q)
include C

theorem path_energy_bound (f : α → ℝ) (x y : α) :
    (C.path x y).edgeSum (fun a b => (f a-f b)^2) ≤
      Q * (C.path x y).edgeSum (fun a b => P.weight a b * (f a-f b)^2) := by
  unfold Path.edgeSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hQ : (0:ℝ)<Q := by exact_mod_cast C.Q_pos
  have h := (div_le_iff₀ hQ).mp (C.transition_lower x y i)
  have hh := mul_le_mul_of_nonneg_right h
    (sq_nonneg (f ((C.path x y).vertex i.castSucc)-f ((C.path x y).vertex i.succ)))
  nlinarith

/-- All-pairs path differences are bounded by the actual weighted energy. -/
theorem pair_energy_bound (f : α → ℝ) :
    (∑ x, ∑ y, (f x-f y)^2) ≤
      (L:ℝ) * Q * K * Fintype.card α * P.energy f := by
  have hpath : ∀ x y, (f x-f y)^2 ≤
      (L:ℝ)*Q*(C.path x y).edgeSum (fun a b => P.weight a b*(f a-f b)^2) := by
    intro x y
    have hn : 0 ≤ (C.path x y).edgeSum (fun a b => (f a-f b)^2) :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc
      _ ≤ (C.path x y).length * (C.path x y).edgeSum (fun a b => (f a-f b)^2) :=
        (C.path x y).difference_sq_le f
      _ ≤ L * (C.path x y).edgeSum (fun a b => (f a-f b)^2) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast C.length_le x y) hn
      _ ≤ L * (Q * (C.path x y).edgeSum (fun a b => P.weight a b*(f a-f b)^2)) :=
        mul_le_mul_of_nonneg_left (C.path_energy_bound f x y) (by positivity)
      _ = _ := by ring
  have ht : (∑ a, ∑ b, (traffic C.path a b : ℝ) *
      (P.weight a b*(f a-f b)^2)) ≤ (K:ℝ)*Fintype.card α * P.energy f := by
    unfold LazyChain.energy
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b _
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast C.traffic_le a b
    · exact mul_nonneg (P.nonneg a b) (sq_nonneg _)
  calc
    _ ≤ ∑ x, ∑ y, (L:ℝ)*Q*(C.path x y).edgeSum
        (fun a b => P.weight a b*(f a-f b)^2) := by
      exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hpath x y
    _ = (L:ℝ)*Q * (∑ x, ∑ y, (C.path x y).edgeSum
        (fun a b => P.weight a b*(f a-f b)^2)) := by simp_rw [Finset.mul_sum]
    _ ≤ (L:ℝ)*Q*((K:ℝ)*Fintype.card α*P.energy f) := by
      rw [sum_edgeSum_eq_traffic]
      exact mul_le_mul_of_nonneg_left ht (by positivity)
    _ = _ := by ring

/-- A convenient integral upper bound for the relaxation scale. -/
def scale (_C : CanonicalPaths P K L Q) : ℕ := max 1 (L*Q*K)

theorem scale_pos : 0 < C.scale := by unfold scale; omega

/-- The Poincaré estimate is a consequence of paths and traffic, not an input. -/
theorem poincare [Nonempty α] (f : α → ℝ) (hf : ∑ x, f x = 0) :
    P.sqNorm f ≤ C.scale * P.energy f := by
  have hn : (0:ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hp := C.pair_energy_bound f
  rw [P.pair_difference_identity f hf] at hp
  have he := P.energy_nonneg f
  have hs : (L:ℝ)*Q*K ≤ C.scale := by
    have h : L*Q*K ≤ max 1 (L*Q*K) := le_max_right _ _
    exact_mod_cast h
  have hp' : 2*P.sqNorm f ≤ (L:ℝ)*Q*K*P.energy f := by
    apply (mul_le_mul_iff_right₀ hn).mp
    calc
      (Fintype.card α : ℝ)*(2*P.sqNorm f) = 2*Fintype.card α*P.sqNorm f := by ring
      _ ≤ (L:ℝ)*Q*K*Fintype.card α*P.energy f := hp
      _ = _ := by ring
  have hs' := mul_le_mul_of_nonneg_right hs he
  have hnorm := P.sqNorm_nonneg f
  linarith

end CanonicalPaths
end HiddenCircuits.Approximation.FiniteChains
