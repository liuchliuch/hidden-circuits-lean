import HiddenCircuits.DH.ArrayColumn
import Mathlib.Data.Nat.Size

/-! Executable integer coefficient arrays for arbitrary spectral interpolation nodes. -/
namespace HiddenCircuits.Circuit.IntegerSpectralWeights
open Polynomial
open scoped BigOperators

/-- Integer coefficient recurrence, with zero outside the polynomial support. -/
def coeffs : List ℤ → ℕ → ℤ
  | [],k => if k=0 then 1 else 0
  | a::xs,0 => -a*coeffs xs 0
  | a::xs,k+1 => coeffs xs k-a*coeffs xs (k+1)

noncomputable def poly (xs : List ℤ) : ℤ[X] := (xs.map (fun a => X-C a)).prod

theorem coeffs_eq (xs : List ℤ) (k : ℕ) : coeffs xs k=(poly xs).coeff k := by
  induction xs generalizing k with
  | nil => simp [poly,coeffs,coeff_one]
  | cons a xs ih =>
    change coeffs (a::xs) k=((X-C a)*poly xs).coeff k
    cases k with
    | zero => simp only [coeffs,sub_mul,coeff_sub,coeff_C_mul,coeff_X_mul_zero,←ih,zero_sub,neg_mul]
    | succ k => simp only [coeffs,sub_mul,coeff_sub,coeff_C_mul,coeff_X_mul,←ih]

theorem coeffs_zero (xs : List ℤ) (k : ℕ) (hk : xs.length<k) : coeffs xs k=0 := by
  induction xs generalizing k with
  | nil => simp [coeffs,show k≠0 by simp at hk; omega]
  | cons a xs ih =>
    cases k with
    | zero => simp at hk
    | succ k => simp only [coeffs,ih k (by simp at hk; omega),ih (k+1) (by simp at hk; omega),mul_zero,sub_zero]

open HiddenCircuits.DH.ArrayColumn

def arrayEntry (a : ℤ) (c : Array ℤ) (k : ℕ) : Counted ℤ :=
  let m := mul a (read c k)
  let d := sub (if k=0 then 0 else read c (k-1)) m.value
  ⟨d.value,m.operations+d.operations⟩

def arrayRun : List ℤ → Counted (Array ℤ)
  | [] => ⟨#[1],0⟩
  | a::xs =>
    let old := arrayRun xs
    let next := scan (arrayEntry a old.value) (xs.length+2)
    ⟨next.value,old.operations+next.operations⟩

@[simp] theorem arrayRun_size (xs : List ℤ) : (arrayRun xs).value.size=xs.length+1 := by
  cases xs <;> simp [arrayRun]

theorem arrayRun_read (xs : List ℤ) (k : ℕ) : read (arrayRun xs).value k=coeffs xs k := by
  induction xs generalizing k with
  | nil => by_cases hk:k=0 <;> simp [arrayRun,DH.ArrayColumn.read,coeffs,hk]
  | cons a xs ih =>
    change read (scan (arrayEntry a (arrayRun xs).value) (xs.length+2)).value k=_
    rw [read_scan]
    by_cases hk : k<xs.length+2
    · rw [if_pos hk]
      cases k with
      | zero => simp [arrayEntry,DH.ArrayColumn.mul,DH.ArrayColumn.sub,coeffs,ih]
      | succ k => simp [arrayEntry,DH.ArrayColumn.mul,DH.ArrayColumn.sub,coeffs,ih]
    · rw [if_neg hk,coeffs_zero _ k (by simp; omega)]

theorem arrayRun_operations (xs : List ℤ) :
    (arrayRun xs).operations=xs.length*(xs.length+3) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [arrayRun,scan_operations,arrayEntry,DH.ArrayColumn.mul,DH.ArrayColumn.sub]
    simp only [show (1:ℕ)+1=2 from rfl,Finset.sum_const,Finset.card_range,smul_eq_mul]
    change (arrayRun xs).operations+(xs.length+2)*2=(xs.length+1)*(xs.length+1+3)
    rw [ih]; ring

/-- Every coefficient is bounded by the product of one plus each root magnitude. -/
theorem coeffs_abs_bound (xs : List ℤ) (B : ℤ) (hB : 0≤B)
    (hxs : ∀ a∈xs, |a|≤B) (k : ℕ) : |coeffs xs k|≤(B+1)^xs.length := by
  induction xs generalizing k with
  | nil => by_cases hk:k=0 <;> simp [coeffs,hk]
  | cons a xs ih =>
    have ha := hxs a (by simp)
    have ht : ∀ b∈xs, |b|≤B := fun b hb => hxs b (by simp [hb])
    have hp : 0≤(B+1)^xs.length := pow_nonneg (by omega) _
    cases k with
    | zero =>
      simp only [coeffs,abs_mul,abs_neg,List.length_cons,pow_succ]
      have hh := mul_le_mul ha (ih ht 0) (abs_nonneg _) hB
      nlinarith
    | succ k =>
      have hh := abs_sub (coeffs xs k) (a*coeffs xs (k+1))
      have hm := mul_le_mul ha (ih ht (k+1)) (abs_nonneg _) hB
      rw [abs_mul] at hh
      simp only [coeffs,List.length_cons,pow_succ]
      have hh0 := ih ht k
      nlinarith


/-- The actual integer Lagrange denominator at distinguished node x. -/
def denominator (x : ℤ) (xs : List ℤ) : ℤ := (xs.map (fun a => x-a)).prod

theorem denominator_ne_zero (x : ℤ) (xs : List ℤ) (hx : ∀ a∈xs, x≠a) :
    denominator x xs≠0 := by
  induction xs with
  | nil => simp [denominator]
  | cons a xs ih =>
    simp only [denominator,List.map_cons,List.prod_cons,mul_ne_zero_iff]
    exact ⟨sub_ne_zero.mpr (hx a (by simp)),ih (fun b hb => hx b (by simp [hb]))⟩

theorem denominator_abs_bound (x : ℤ) (xs : List ℤ) (B : ℤ) (hB : 0≤B)
    (hx : |x|≤B) (hxs : ∀ a∈xs, |a|≤B) : |denominator x xs|≤(2*B)^xs.length := by
  induction xs with
  | nil => simp [denominator]
  | cons a xs ih =>
    have ha : |x-a|≤2*B := (abs_sub x a).trans (by have := hxs a (by simp); omega)
    have ht := ih (fun b hb => hxs b (by simp [hb]))
    change |(x-a)*denominator x xs|≤(2*B)^(xs.length+1)
    rw [abs_mul,pow_succ']
    exact mul_le_mul ha ht (abs_nonneg _) (by omega)

theorem coeffs_natAbs_bound (xs : List ℤ) (B : ℕ)
    (hxs : ∀ a∈xs, a.natAbs≤B) (k : ℕ) : (coeffs xs k).natAbs≤(B+1)^xs.length := by
  have hh := coeffs_abs_bound xs (B:ℤ) (by positivity)
    (fun a ha => (show |a|≤(B:ℤ) by rw [←Int.natCast_natAbs]; exact_mod_cast hxs a ha)) k
  rw [←Int.natCast_natAbs] at hh
  exact_mod_cast hh

theorem coeffs_bit_bound (xs : List ℤ) (b : ℕ)
    (hxs : ∀ a∈xs, a.natAbs≤2^b) (k : ℕ) :
    (coeffs xs k).natAbs.size+1≤(b+1)*xs.length+2 := by
  have hh := coeffs_natAbs_bound xs (2^b) hxs k
  have hp : 2^b+1≤2^(b+1) := by have := Nat.one_le_pow b 2 (by decide); simp only [pow_succ]; omega
  have hh' : (coeffs xs k).natAbs≤2^((b+1)*xs.length) :=
    hh.trans ((Nat.pow_le_pow_left hp xs.length).trans_eq (pow_mul 2 (b+1) xs.length).symm)
  have hs := Nat.size_le_size hh'
  rw [Nat.size_pow] at hs
  omega

theorem denominator_bit_bound (x : ℤ) (xs : List ℤ) (b : ℕ)
    (hx : x.natAbs≤2^b) (hxs : ∀ a∈xs, a.natAbs≤2^b) :
    (denominator x xs).natAbs.size+1≤(b+1)*xs.length+2 := by
  have hh := denominator_abs_bound x xs ((2:ℤ)^b) (by positivity)
    (by rw [←Int.natCast_natAbs]; exact_mod_cast hx) (fun a ha => by rw [←Int.natCast_natAbs]; exact_mod_cast hxs a ha)
  have he : (2:ℤ)*2^b=2^(b+1) := by rw [pow_succ']
  rw [he,←pow_mul] at hh
  have hn : (denominator x xs).natAbs≤2^((b+1)*xs.length) := by
    rw [←Int.natCast_natAbs] at hh
    exact_mod_cast hh
  have hs := Nat.size_le_size hn
  rw [Nat.size_pow] at hs
  omega

end HiddenCircuits.Circuit.IntegerSpectralWeights
