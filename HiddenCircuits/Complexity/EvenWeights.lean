import HiddenCircuits.Complexity.InterpolationWeights
import HiddenCircuits.GraphReduction.CliqueProbeInterpolation

/-! Fresh reconstruction: exact integer Lagrange weights at the actual even
nodes 0,2,...,2d, with unconditional polynomial bit bounds. -/
namespace HiddenCircuits.Complexity.EvenWeights
open scoped BigOperators
open Polynomial GraphReduction

def numerator (d : ℕ) (i : Fin (d+1)) : ℤ := ∏j∈Finset.univ.erase i,((-1:ℤ)-2*j.val)
def denominator (d : ℕ) (i : Fin (d+1)) : ℤ := (2:ℤ)^d*interpolationDenominator d i

lemma denominator_product (d : ℕ) (i : Fin (d+1)) :
    denominator d i=∏j∈Finset.univ.erase i,((2:ℤ)*i.val-2*j.val) := by
  simp only [denominator,interpolationDenominator]
  rw [show (∏j∈Finset.univ.erase i,((2:ℤ)*i.val-2*j.val))=
    ∏j∈Finset.univ.erase i,((2:ℤ)*(i.val-j.val)) by apply Finset.prod_congr rfl;intro j hj;ring]
  rw [Finset.prod_mul_distrib]
  simp
lemma denominator_ne_zero (d : ℕ) (i : Fin (d+1)) : denominator d i≠0 :=
  mul_ne_zero (pow_ne_zero _ (by decide)) (interpolationDenominator_ne_zero _ _)
lemma numerator_natAbs (d : ℕ) (i : Fin (d+1)) : (numerator d i).natAbs≤(2*d+1)^d := by
  unfold numerator
  change Int.natAbsHom (∏j∈Finset.univ.erase i,((-1:ℤ)-2*j.val))≤_
  rw [map_prod]
  calc
    _≤∏_j∈Finset.univ.erase i,(2*d+1) := by
      apply Finset.prod_le_prod'
      intro j hj
      change ((-1:ℤ)-2*j.val).natAbs≤_
      have he : (-1:ℤ)-2*j.val=-((2*j.val+1:ℕ):ℤ) := by push_cast;ring
      rw [he]
      simp only [Int.natAbs_neg,Int.natAbs_natCast]
      have hj:=j.isLt;omega
    _=_ := by simp
lemma denominator_natAbs (d : ℕ) (i : Fin (d+1)) : (denominator d i).natAbs≤(2*d+1)^d := by
  simp only [denominator,Int.natAbs_mul,Int.natAbs_pow]
  calc
    _≤2^d*d^d := Nat.mul_le_mul_left _ (interpolationDenominator_natAbs d i)
    _=(2*d)^d := (mul_pow _ _ _).symm
    _≤_ := Nat.pow_le_pow_left (by omega) _
lemma envelope (d : ℕ) (i : Fin (d+1)) :
    (numerator d i).natAbs≤2^(2*d^2+1) ∧ (denominator d i).natAbs≤2^(2*d^2+1) := by
  have hbase := Nat.pow_le_pow_left (succ_le_two_pow (2*d)) d
  have he : (2^(2*d))^d=2^(2*d^2) := by rw [←pow_mul];congr 1;ring
  rw [he] at hbase
  have hpow : 2^(2*d^2)≤2^(2*d^2+1) := Nat.pow_le_pow_right (by decide) (by omega)
  exact ⟨(numerator_natAbs d i).trans (hbase.trans hpow),(denominator_natAbs d i).trans (hbase.trans hpow)⟩
@[simp] lemma numerator_cast (d : ℕ) (i : Fin (d+1)) :
    (numerator d i:ℚ)=∏j∈Finset.univ.erase i,((-1:ℚ)-cliqueInterpolationNode j) := by
  simp [numerator,cliqueInterpolationNode]
@[simp] lemma denominator_cast (d : ℕ) (i : Fin (d+1)) :
    (denominator d i:ℚ)=∏j∈Finset.univ.erase i,(cliqueInterpolationNode i-cliqueInterpolationNode j) := by
  rw [denominator_product]
  simp [cliqueInterpolationNode]
lemma basis_negative (d : ℕ) (i : Fin (d+1)) :
    (Lagrange.basis Finset.univ cliqueInterpolationNode i).eval (-1)=
      (numerator d i:ℚ)/(denominator d i:ℚ) := by
  simp only [Lagrange.basis,Lagrange.basisDivisor,eval_prod,eval_mul,eval_C,eval_sub,eval_X,
    Finset.prod_mul_distrib,Finset.prod_inv_distrib,numerator_cast,denominator_cast,div_eq_mul_inv]
  exact mul_comm _ _
lemma interpolation_negative (d : ℕ) (f : Fin (d+1)→ℚ) :
    (interpolateCliqueValues d f).eval (-1)=∑i,f i*(numerator d i:ℚ)/(denominator d i:ℚ) := by
  simp only [interpolateCliqueValues,Lagrange.interpolate_apply,eval_finset_sum,eval_mul,eval_C,
    basis_negative,div_eq_mul_inv,mul_assoc]


lemma oddFactorial_eq_product (d : ℕ) : oddFactorial (d+1)=∏j:Fin (d+1),(2*j.val+1) := by
  simpa only [oddFactorial] using (Fin.prod_univ_eq_prod_range (fun j => 2*j+1) (d+1)).symm
lemma oddFactorial_split (d : ℕ) (i : Fin (d+1)) :
    oddFactorial (d+1)=(2*i.val+1)*(∏j∈Finset.univ.erase i,(2*j.val+1)) := by
  rw [oddFactorial_eq_product]
  exact (Finset.mul_prod_erase Finset.univ (fun j:Fin (d+1) => 2*j.val+1) (Finset.mem_univ i)).symm
lemma divisor_dvd (d : ℕ) (i : Fin (d+1)) : (2*i.val+1)∣oddFactorial (d+1) := by
  exact ⟨_,oddFactorial_split d i⟩
lemma oddFactorial_quotient (d : ℕ) (i : Fin (d+1)) :
    oddFactorial (d+1)/(2*i.val+1)=∏j∈Finset.univ.erase i,(2*j.val+1) := by
  rw [oddFactorial_split]
  exact Nat.mul_div_right _ (by omega)
lemma numerator_eq (d : ℕ) (i : Fin (d+1)) :
    numerator d i=(-1:ℤ)^d*((oddFactorial (d+1)/(2*i.val+1):ℕ):ℤ) := by
  rw [oddFactorial_quotient]
  unfold numerator
  have he : (fun j:Fin (d+1) => (-1:ℤ)-2*j.val)=(fun j => (-1:ℤ)*((2*j.val+1:ℕ):ℤ)) := by
    funext j;push_cast;ring
  rw [he,Finset.prod_mul_distrib]
  simp
end HiddenCircuits.Complexity.EvenWeights
