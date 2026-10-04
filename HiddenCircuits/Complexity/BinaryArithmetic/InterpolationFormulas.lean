import HiddenCircuits.Complexity.InterpolationWeights
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Consecutive-node interpolation weights reduce to concrete factorials,
products, parity signs, and one proved-exact natural division. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic
open scoped BigOperators

private theorem denominator_range (i k : ℕ) :
    (∏ j ∈ Finset.range (i+k+1), if j=i then (1 : ℤ) else (i : ℤ)-j) =
      (-1 : ℤ)^k*(i.factorial : ℤ)*(k.factorial : ℤ) := by
  induction k with
  | zero =>
    simp only [Nat.add_zero,Finset.prod_range_succ,ite_true,mul_one,pow_zero,one_mul,Nat.factorial_zero,Nat.cast_one]
    have he : (∏ j ∈ Finset.range i, if j=i then (1 : ℤ) else (i : ℤ)-j) =
        ∏ j ∈ Finset.range i, ((i : ℤ)-j) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [if_neg (by have := Finset.mem_range.mp hj; omega)]
    rw [he,Finset.prod_range_natCast_sub,←Nat.descFactorial_eq_prod_range,Nat.descFactorial_self]
  | succ k ih =>
    have hn : i+(k+1)+1=(i+k+1)+1 := by omega
    rw [hn,Finset.prod_range_succ,ih,if_neg (by omega)]
    simp only [Nat.cast_add,Nat.cast_one,Nat.factorial_succ,Nat.cast_mul,pow_succ]
    ring

/-- The signed Lagrange denominator at node i is exactly the two-factorial formula. -/
theorem interpolationDenominator_factorial (d : ℕ) (i : Fin (d+1)) :
    interpolationDenominator d i =
      (-1 : ℤ)^(d-i.val)*(i.val.factorial : ℤ)*((d-i.val).factorial : ℤ) := by
  have he : interpolationDenominator d i =
      ∏ j : Fin (d+1), if j=i then (1 : ℤ) else (i.val : ℤ)-j.val := by
    unfold interpolationDenominator
    rw [←Finset.prod_erase (Finset.univ : Finset (Fin (d+1))) (a := i)
      (f := fun j => if j=i then (1 : ℤ) else (i.val : ℤ)-j.val) (by simp)]
    apply Finset.prod_congr rfl
    intro j hj
    rw [if_neg (Finset.mem_erase.mp hj).1]
  rw [he]
  have hf : (∏ j : Fin (d+1), if j=i then (1 : ℤ) else (i.val : ℤ)-j.val) =
      ∏ j : Fin (d+1), if j.val=i.val then (1 : ℤ) else (i.val : ℤ)-j.val := by
    apply Finset.prod_congr rfl
    intro j _
    simp [Fin.ext_iff]
  rw [hf,Fin.prod_univ_eq_prod_range (fun j : ℕ => if j=i.val then (1 : ℤ) else (i.val : ℤ)-j) (d+1)]
  have hd : Finset.range (d+1)=Finset.range (i.val+(d-i.val)+1) := congrArg Finset.range (by omega)
  rw [hd]
  exact denominator_range i.val (d-i.val)

private theorem positive_erase_product (d : ℕ) (i : Fin (d+1)) :
    (∏ j ∈ Finset.univ.erase i, (j.val+1))=(d+1).factorial/(i.val+1) := by
  have h := Finset.mul_prod_erase (Finset.univ : Finset (Fin (d+1)))
    (fun j => j.val+1) (Finset.mem_univ i)
  have hfull : (∏ j : Fin (d+1), (j.val+1))=(d+1).factorial :=
    (Fin.prod_univ_eq_prod_range (fun j : ℕ => j+1) (d+1)).trans (Finset.prod_range_add_one_eq_factorial (d+1))
  rw [hfull] at h
  have hh := congrArg (fun x => x/(i.val+1)) h
  simpa using hh

/-- The negative-evaluation numerator uses a factorial quotient with no remainder. -/
theorem interpolationNegativeNumerator_factorial (d : ℕ) (i : Fin (d+1)) :
    interpolationNegativeNumerator d i =
      (-1 : ℤ)^d*((d+1).factorial/(i.val+1) : ℕ) := by
  unfold interpolationNegativeNumerator
  have he : (∏ j ∈ Finset.univ.erase i, ((-1 : ℤ)-j.val)) =
      ∏ j ∈ Finset.univ.erase i, -((j.val+1 : ℕ) : ℤ) := by
    apply Finset.prod_congr rfl
    intro j _
    push_cast
    ring
  rw [he,Finset.prod_neg]
  simp only [Finset.card_erase_of_mem (Finset.mem_univ i),Finset.card_univ,Fintype.card_fin,Nat.add_sub_cancel]
  congr 1
  rw [←Nat.cast_prod,positive_erase_product]

/-- Exactness for the natural quotient in the negative-evaluation weight. -/
theorem interpolationNegativeNumerator_divisible (d : ℕ) (i : Fin (d+1)) :
    i.val+1 ∣ (d+1).factorial := Nat.dvd_factorial (by omega) (by omega)

end HiddenCircuits.Complexity.BinaryArithmetic
