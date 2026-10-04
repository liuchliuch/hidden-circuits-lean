import HiddenCircuits.Circuit.IntegerSpectralWeights
import HiddenCircuits.Circuit.SpectralRecovery

/-! Actual integer coefficient arrays implement every Lagrange coefficient at explicit integer nodes. -/
namespace HiddenCircuits.Circuit.LagrangeIntegerArrays
open scoped BigOperators
open Polynomial
open IntegerSpectralWeights
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def otherNodes (l : List ι) (node : ι → ℤ) (i : ι) : List ℤ :=
  (l.filter (fun j => j≠i)).map node

def basisDenominator (l : List ι) (node : ι → ℤ) (i : ι) : ℤ :=
  denominator (node i) (otherNodes l node i)

def basisNumerator (l : List ι) (node : ι → ℤ) (i : ι) (k : ℕ) : ℤ :=
  coeffs (otherNodes l node i) k

 theorem otherNodes_prod {R : Type*} [CommMonoid R] (l : List ι) (hl : l.Nodup)
    (hall : ∀ i, i∈l) (node : ι → ℤ) (i : ι) (f : ℤ → R) :
    ((otherNodes l node i).map f).prod=∏ j ∈ Finset.univ.erase i, f (node j) := by
  have he : (l.filter (fun j => j≠i)).toFinset=Finset.univ.erase i := by
    ext j
    simp [hall j]
  unfold otherNodes
  rw [List.map_map,← List.prod_toFinset _ (hl.filter _),he]
  rfl

 theorem basisDenominator_cast (l : List ι) (hl : l.Nodup) (hall : ∀ i, i∈l)
    (node : ι → ℤ) (i : ι) :
    (basisDenominator l node i : ℚ)=∏ j ∈ Finset.univ.erase i, ((node i:ℚ)-(node j:ℚ)) := by
  unfold basisDenominator denominator
  push_cast
  rw [List.map_map]
  have hf : (Int.cast ∘ fun a : ℤ => node i-a)=(fun a : ℤ => (node i:ℚ)-(a:ℚ)) := by
    funext a
    exact Int.cast_sub _ _
  rw [hf]
  exact otherNodes_prod l hl hall node i (fun a => (node i:ℚ)-(a:ℚ))

 theorem poly_cast (l : List ι) (hl : l.Nodup) (hall : ∀ i, i∈l) (node : ι → ℤ) (i : ι) :
    (poly (otherNodes l node i)).map (Int.castRingHom ℚ)=
      ∏ j ∈ Finset.univ.erase i, (X-C (node j:ℚ)) := by
  unfold poly
  rw [Polynomial.map_list_prod,List.map_map]
  have hf : (Polynomial.map (Int.castRingHom ℚ) ∘ fun a : ℤ => X-C a)=
      (fun a : ℤ => (X-C (a:ℚ))) := by
    funext a
    simp only [Function.comp_apply,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C]
    rfl
  rw [hf]
  exact otherNodes_prod l hl hall node i (fun a => (X-C (a:ℚ)))

 theorem basis_polynomial (l : List ι) (hl : l.Nodup) (hall : ∀ i, i∈l)
    (node : ι → ℤ) (i : ι) :
    Lagrange.basis Finset.univ (fun j => (node j:ℚ)) i=
      C ((basisDenominator l node i:ℚ)⁻¹)*(poly (otherNodes l node i)).map (Int.castRingHom ℚ) := by
  rw [poly_cast l hl hall,basisDenominator_cast l hl hall]
  simp only [Lagrange.basis,Lagrange.basisDivisor,Finset.prod_mul_distrib,
    ← map_prod,Finset.prod_inv_distrib]

/-- The finite Lagrange basis coefficients are literal ratios of the computed integer entries. -/
theorem basis_coefficient (l : List ι) (hl : l.Nodup) (hall : ∀ i, i∈l)
    (node : ι → ℤ) (i : ι) (k : ℕ) :
    (Lagrange.basis Finset.univ (fun j => (node j:ℚ)) i).coeff k=
      (basisNumerator l node i k:ℚ)/(basisDenominator l node i:ℚ) := by
  rw [basis_polynomial l hl hall,coeff_C_mul,coeff_map]
  simp only [basisNumerator,coeffs_eq,div_eq_mul_inv,mul_comm]
  rfl

/-- Every coefficient of the actual interpolant is computed by the integer basis arrays. -/
theorem interpolate_coefficient (l : List ι) (hl : l.Nodup) (hall : ∀ i, i∈l)
    (node : ι → ℤ) (target : ι → ℚ) (k : ℕ) :
    (Lagrange.interpolate Finset.univ (fun j => (node j:ℚ)) target).coeff k=
      ∑ i, target i*((basisNumerator l node i k:ℚ)/(basisDenominator l node i:ℚ)) := by
  simp only [Lagrange.interpolate_apply,finset_sum_coeff,coeff_C_mul,basis_coefficient l hl hall]

 theorem basisDenominator_ne_zero (l : List ι) (node : ι → ℤ) (hinj : Function.Injective node) (i : ι) :
    basisDenominator l node i≠0 := by
  apply denominator_ne_zero
  intro a ha
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
  have hji := (List.mem_filter.mp hj).2
  exact fun h => (of_decide_eq_true hji) (hinj h.symm)

 theorem basis_bounds (l : List ι) (node : ι → ℤ) (b : ℕ)
    (hb : ∀ i, (node i).natAbs ≤ 2^b) (i : ι) (k : ℕ) :
    (basisNumerator l node i k).natAbs.size+1 ≤ (b+1)*l.length+2 ∧
      (basisDenominator l node i).natAbs.size+1 ≤ (b+1)*l.length+2 := by
  have hnodes : ∀ a∈otherNodes l node i, a.natAbs ≤ 2^b := by
    intro a ha
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp ha
    exact hb j
  have hlen : (otherNodes l node i).length ≤ l.length := by
    simp only [otherNodes,List.length_map]
    exact List.length_filter_le _ _
  exact ⟨(coeffs_bit_bound _ b hnodes k).trans (by gcongr),
    (denominator_bit_bound _ _ b (hb i) hnodes).trans (by gcongr)⟩

end HiddenCircuits.Circuit.LagrangeIntegerArrays
