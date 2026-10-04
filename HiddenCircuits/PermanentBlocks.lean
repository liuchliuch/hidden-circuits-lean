import HiddenCircuits.Transfers
import Mathlib.GroupTheory.Perm.Finite

namespace HiddenCircuits
open scoped BigOperators

/-- Relabeling both sides of a square matrix does not change its permanent. -/
theorem permanent_submatrix_equiv {A B R : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [CommSemiring R]
    (M : Matrix A A R) (e : B ≃ A) : (M.submatrix e e).permanent = M.permanent := by
  unfold Matrix.permanent
  refine Fintype.sum_equiv (Equiv.permCongr e) _ _ ?_
  intro σ
  refine Fintype.prod_equiv e _ _ ?_
  intro b
  simp

/-- Rows and columns can be independently relabeled, unlike the signed determinant. -/
theorem permanent_submatrix_two_equiv {A B R : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [CommSemiring R]
    (M : Matrix A A R) (er ec : B ≃ A) : (M.submatrix er ec).permanent = M.permanent := by
  have hm : M.submatrix er ec = (M.submatrix er er).submatrix id (ec.trans er.symm) := by
    ext i j
    simp
  rw [hm,Matrix.permanent_permute_rows,permanent_submatrix_equiv]

/-- The actual permanent of an upper block-triangular matrix factors.
The proof excludes every mixed permutation using its forbidden backward edge. -/
theorem permanent_block_upper {A B R : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [CommSemiring R]
    (M : Matrix (A ⊕ B) (A ⊕ B) R)
    (hlower : ∀ b a, M (Sum.inr b) (Sum.inl a) = 0) :
    M.permanent = (M.submatrix Sum.inl Sum.inl).permanent *
      (M.submatrix Sum.inr Sum.inr).permanent := by
  classical
  let f : Equiv.Perm (A ⊕ B) → R := fun σ => ∏ x, M (σ x) x
  let e := Equiv.Perm.sumCongrHom A B
  have hzero : ∀ σ ∈ Finset.univ, σ ∉ Finset.univ.image e → f σ = 0 := by
    intro σ _ hout
    by_contra hn
    have hm : Set.MapsTo σ (Set.range Sum.inl) (Set.range Sum.inl) := by
      rintro x ⟨a,rfl⟩
      cases hs:σ (Sum.inl a) with
      | inl a' => exact ⟨a',rfl⟩
      | inr b =>
        exfalso
        apply hn
        apply Finset.prod_eq_zero (Finset.mem_univ (Sum.inl a))
        rw [hs,hlower]
    obtain ⟨p,hp⟩ := (MonoidHom.mem_range.mp
      (Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hm))
    exact hout (Finset.mem_image.mpr ⟨p,Finset.mem_univ p,hp⟩)
  change (∑ σ, f σ) = _
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e)) hzero]
  rw [Finset.sum_image Equiv.Perm.sumCongrHom_injective.injOn]
  simp only [f,e,Equiv.Perm.sumCongrHom_apply,Fintype.prod_sum_type,
    Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr]
  rw [Fintype.sum_prod_type]
  unfold Matrix.permanent
  simp only [Matrix.submatrix_apply]
  exact (Finset.sum_mul_sum ..).symm

/-- Same statement with explicit four blocks, including arbitrary forward cross edges. -/
theorem permanent_fromBlocks {A B R : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [CommSemiring R]
    (M : Matrix A A R) (F : Matrix A B R) (N : Matrix B B R) :
    (Matrix.fromBlocks M F 0 N).permanent = M.permanent * N.permanent := by
  simpa using permanent_block_upper (Matrix.fromBlocks M F 0 N) (by intros; rfl)

end HiddenCircuits
