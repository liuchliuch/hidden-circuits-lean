import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-!
A matrix whose nonzero entries strictly increase an integer potential is nilpotent
with an exponent bounded by the range of that potential, not by its dimension.
This is the path bound needed for the paper's exponentially large subset spaces.
-/
namespace HiddenCircuits
open scoped BigOperators

section Potential
variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- Every nonzero entry of the `a`th power witnesses at least `a` units of flow. -/
theorem potential_pow_support (B : Matrix ι ι R) (ω : ι → ℕ)
    (hB : ∀ i j, B i j ≠ 0 → ω i + 1 ≤ ω j) :
    ∀ a i j, (B ^ a) i j ≠ 0 → ω i + a ≤ ω j := by
  intro a
  induction a with
  | zero =>
      intro i j h
      have hij : i = j := by
        by_contra hne
        exact h (by simp [hne])
      subst j
      simp
  | succ a ih =>
      intro i j h
      rw [pow_succ, Matrix.mul_apply] at h
      obtain ⟨z, _, hz⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
      have hleft : (B ^ a) i z ≠ 0 := fun he => hz (by rw [he, zero_mul])
      have hright : B z j ≠ 0 := fun he => hz (by rw [he, mul_zero])
      have h₁ := ih i z hleft
      have h₂ := hB z j hright
      omega

/-- A potential of range width `d` supplies the concrete nilpotence bound `d+1`. -/
theorem potential_nilpotent (B : Matrix ι ι R) (ω : ι → ℕ) (lo d : ℕ)
    (hB : ∀ i j, B i j ≠ 0 → ω i + 1 ≤ ω j)
    (hlo : ∀ i, lo ≤ ω i) (hhi : ∀ i, ω i ≤ lo + d) :
    B ^ (d + 1) = 0 := by
  ext i j
  by_contra h
  have hs := potential_pow_support B ω hB (d + 1) i j h
  have hl := hlo i
  have hh := hhi j
  omega

/-- The finite, division-free inverse used throughout the transfer construction. -/
def inverseSeries (B : Matrix ι ι R) (d : ℕ) : Matrix ι ι R :=
  ∑ a ∈ Finset.range (d + 1), (-B) ^ a

theorem inverseSeries_mul (B : Matrix ι ι R) (d : ℕ)
    (h : B ^ (d + 1) = 0) : inverseSeries B d * (1 + B) = 1 := by
  have hn : (-B) ^ (d + 1) = 0 := by rw [neg_pow, h, mul_zero]
  simpa [inverseSeries, hn] using geom_sum_mul_neg (-B) (d + 1)

theorem mul_inverseSeries (B : Matrix ι ι R) (d : ℕ)
    (h : B ^ (d + 1) = 0) : (1 + B) * inverseSeries B d = 1 := by
  have hn : (-B) ^ (d + 1) = 0 := by rw [neg_pow, h, mul_zero]
  simpa [inverseSeries, hn] using mul_neg_geom_sum (-B) (d + 1)

end Potential
end HiddenCircuits
