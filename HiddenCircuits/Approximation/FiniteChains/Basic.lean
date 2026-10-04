import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Finite reversible chains and concrete paths

All transition weights and paths are actual data. The estimates in this
subtree are proved by finite sums; no spectral or mixing certificate is an
input to the chain definition.
-/
namespace HiddenCircuits.Approximation.FiniteChains
open scoped BigOperators

variable {α : Type*} [Fintype α]

/-- A finite symmetric stochastic transition matrix with holding probability
at least one half. Rational transition tables embed into this structure. -/
structure LazyChain (α : Type*) [Fintype α] where
  weight : α → α → ℝ
  nonneg : ∀ x y, 0 ≤ weight x y
  row_sum : ∀ x, ∑ y, weight x y = 1
  symmetric : ∀ x y, weight x y = weight y x
  lazy : ∀ x, (1:ℝ)/2 ≤ weight x x

namespace LazyChain
variable (P : LazyChain α)

def act (f : α → ℝ) (x : α) : ℝ := ∑ y, P.weight x y * f y

def sqNorm (_P : LazyChain α) (f : α → ℝ) : ℝ := ∑ x, f x ^ 2

def energy (f : α → ℝ) : ℝ :=
  ∑ x, ∑ y, P.weight x y * (f x - f y)^2

@[simp] theorem column_sum (y : α) : ∑ x, P.weight x y = 1 := by
  simp_rw [P.symmetric _ y]
  exact P.row_sum y

theorem act_sum (f : α → ℝ) : ∑ x, P.act f x = ∑ x, f x := by
  simp only [act]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, P.column_sum, one_mul]

theorem sqNorm_nonneg (f : α → ℝ) : 0 ≤ P.sqNorm f :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem energy_nonneg (f : α → ℝ) : 0 ≤ P.energy f :=
  Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    mul_nonneg (P.nonneg x y) (sq_nonneg _)

end LazyChain

/-- A concrete finite path, retaining every vertex and repeated edge. -/
structure Path (x y : α) where
  length : ℕ
  vertex : Fin (length+1) → α
  first : vertex 0 = x
  last : vertex (Fin.last length) = y

namespace Path
variable {x y : α}

noncomputable def edgeCount (p : Path x y) (a b : α) : ℕ := by
  classical
  exact (Finset.univ.filter fun i : Fin p.length =>
    p.vertex i.castSucc = a ∧ p.vertex i.succ = b).card

def edgeSum (p : Path x y) (g : α → α → ℝ) : ℝ :=
  ∑ i : Fin p.length, g (p.vertex i.castSucc) (p.vertex i.succ)

/-- Telescoping along a path does not assume simple or nonrepeating paths. -/
theorem sum_differences (p : Path x y) (f : α → ℝ) :
    p.edgeSum (fun a b => f a - f b) = f x - f y := by
  have htel : ∀ (n : ℕ) (v : Fin (n+1) → ℝ),
      (∑ i : Fin n, (v i.castSucc - v i.succ)) = v 0 - v (Fin.last n) := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [Fin.sum_univ_succ]
      have h := ih (fun i => v i.succ)
      have he : (∑ i : Fin n, (v i.succ.castSucc - v i.succ.succ)) =
          v (0 : Fin (n+1)).succ - v (Fin.last n).succ := by
        simpa only [Fin.succ_castSucc] using h
      rw [he]
      simp only [Fin.castSucc_zero, Fin.succ_last]
      ring
  simpa only [edgeSum,p.first,p.last] using htel p.length (fun i => f (p.vertex i))

theorem difference_sq_le (p : Path x y) (f : α → ℝ) :
    (f x - f y)^2 ≤ p.length * p.edgeSum (fun a b => (f a-f b)^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin p.length))
    (fun _ => (1:ℝ)) (fun i => f (p.vertex i.castSucc) - f (p.vertex i.succ))
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one] at h
  change (p.edgeSum (fun a b => f a-f b))^2 ≤ _ at h
  rw [p.sum_differences] at h
  exact h

theorem edgeSum_eq_count (p : Path x y) (g : α → α → ℝ) :
    p.edgeSum g = ∑ a, ∑ b, (p.edgeCount a b : ℝ) * g a b := by
  classical
  calc
    p.edgeSum g = ∑ i : Fin p.length, ∑ a, ∑ b,
        if p.vertex i.castSucc = a ∧ p.vertex i.succ = b then g a b else 0 := by
      simp [edgeSum,ite_and,eq_comm]
    _ = ∑ a, ∑ b, ∑ i : Fin p.length,
        if p.vertex i.castSucc = a ∧ p.vertex i.succ = b then g a b else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := by
      simp only [edgeCount,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,
        Nat.cast_one,Nat.cast_zero,Finset.sum_mul,ite_mul,one_mul,zero_mul]

end Path
end HiddenCircuits.Approximation.FiniteChains
