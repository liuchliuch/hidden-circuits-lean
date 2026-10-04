import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic

/-! Elementary finite-dimensional ingredients for the Tutte test.
An odd skew matrix is singular, and independent vectors sent into a coordinate
set by an invertible matrix cannot outnumber that coordinate set. -/
namespace HiddenCircuits.Approximation.Initialization.SkewLinear
open scoped BigOperators Matrix
open Matrix Module

theorem odd_det_zero {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℚ) (hA : A.transpose = -A)
    (hodd : Odd (Fintype.card V)) : A.det = 0 := by
  have h := Matrix.det_transpose A
  rw [hA, Matrix.det_neg, hodd.neg_one_pow] at h
  linarith

theorem odd_kernel {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℚ) (hA : A.transpose = -A)
    (hodd : Odd (Fintype.card V)) : ∃ v ≠ 0, A *ᵥ v = 0 :=
  Matrix.exists_mulVec_eq_zero_iff.mpr (odd_det_zero A hA hodd)

theorem independent_of_separating_coordinates {C V : Type*} [Fintype C]
    (v : C → V → ℚ)
    (h : ∀ c, ∃ i, v c i ≠ 0 ∧ ∀ d, d ≠ c → v d i = 0) :
    LinearIndependent ℚ v := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha c
  obtain ⟨i, hi, hd⟩ := h c
  have he := congrFun ha i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at he
  have hs : (∑ d, a d * v d i) = a c * v c i := by
    apply Finset.sum_eq_single c
    · intro d _ hdc
      rw [hd d hdc, mul_zero]
    · simp
  rw [hs] at he
  exact (mul_eq_zero.mp he).resolve_right hi

theorem independent_count_le_coordinates {C V : Type*} [Fintype C] [Fintype V]
    [DecidableEq V] (A : Matrix V V ℚ) (hA : A.det ≠ 0)
    (S : Set V) (v : C → V → ℚ) (hi : LinearIndependent ℚ v)
    (hz : ∀ c i, i ∉ S → (A *ᵥ v c) i = 0) :
    Fintype.card C ≤ Nat.card S := by
  classical
  letI := Fintype.ofFinite S
  let f : (C → ℚ) →ₗ[ℚ] (S → ℚ) :=
    (LinearMap.pi fun i : S => LinearMap.proj i.val).comp
      (A.mulVecLin.comp (Fintype.linearCombination ℚ v))
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro a ha
    have hm : A *ᵥ (Fintype.linearCombination ℚ v a) = 0 := by
      ext i
      by_cases hs : i ∈ S
      · exact congrFun ha ⟨i, hs⟩
      · change (A.mulVecLin (Fintype.linearCombination ℚ v a)) i = 0
        simp only [Fintype.linearCombination_apply, map_sum, map_smul,
          Finset.sum_apply, Pi.smul_apply, Matrix.mulVecLin_apply]
        simp [hz, hs]
    have hc : Fintype.linearCombination ℚ v a = 0 :=
      Matrix.eq_zero_of_mulVec_eq_zero hA hm
    apply hi.fintypeLinearCombination_injective
    simpa using hc
  have hh := LinearMap.finrank_le_finrank_of_injective hf
  simpa [Nat.card_eq_fintype_card] using hh

end HiddenCircuits.Approximation.Initialization.SkewLinear
