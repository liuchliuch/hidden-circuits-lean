import HiddenCircuits.Complexity.BinaryArithmetic.AccumulatorBounds
import Mathlib.Data.Rat.Cast.Lemmas

/-! Exact, unreduced integer
fraction accumulation and bounds on every physical accumulator prefix. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic.RationalAccumulator

abbrev Ratio := ℤ × ℤ

def value (a : Ratio) : ℚ := (a.1 : ℚ) / a.2
def step (a b : Ratio) : Ratio := (a.1*b.2+b.1*a.2, a.2*b.2)
def run (a : Ratio) (xs : List Ratio) : Ratio := xs.foldl step a

@[simp] theorem run_nil (a : Ratio) : run a [] = a := rfl
@[simp] theorem run_cons (a b : Ratio) (xs : List Ratio) : run a (b::xs) = run (step a b) xs := rfl
lemma run_append (a : Ratio) (xs ys : List Ratio) : run a (xs++ys)=run (run a xs) ys := by
  simp [run,List.foldl_append]
lemma foldl_run_flatten (xs : List (List Ratio)) (a : Ratio) : xs.foldl run a=run a xs.flatten := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons,List.flatten_cons,run_append,ih]

lemma step_nonzero (a b : Ratio) (ha : a.2≠0) (hb : b.2≠0) : (step a b).2≠0 := mul_ne_zero ha hb
lemma run_nonzero (a : Ratio) (xs : List Ratio) (ha : a.2≠0) (hs : ∀b∈xs,b.2≠0) : (run a xs).2≠0 := by
  induction xs generalizing a with
  | nil => exact ha
  | cons b xs ih => exact ih (step a b) (step_nonzero a b ha (hs b (by simp))) (by intro z hz;exact hs z (by simp [hz]))
lemma step_value (a b : Ratio) (ha : a.2≠0) (hb : b.2≠0) : value (step a b)=value a+value b := by
  have ha' : (a.2:ℚ)≠0 := by exact_mod_cast ha
  have hb' : (b.2:ℚ)≠0 := by exact_mod_cast hb
  simp only [value,step,Int.cast_add,Int.cast_mul]
  field_simp
lemma run_value (a : Ratio) (xs : List Ratio) (ha : a.2≠0) (hs : ∀b∈xs,b.2≠0) :
    value (run a xs)=value a+(xs.map value).sum := by
  induction xs generalizing a with
  | nil => simp
  | cons b xs ih =>
    rw [run_cons,ih _ (step_nonzero a b ha (hs b (by simp))) (by intro z hz;exact hs z (by simp [hz])),step_value a b ha (hs b (by simp))]
    simp only [List.map_cons,List.sum_cons]
    ring

def Bounded (B : ℕ) (a : Ratio) : Prop := (signedBits a.1).length≤B ∧ (signedBits a.2).length≤B

def BitBound (B : ℕ) : Ratio → List Ratio → Prop
  | a, [] => Bounded B a
  | a, b::xs => Bounded B a ∧ Bounded B b ∧ BitBound B (step a b) xs

lemma BitBound.head {B : ℕ} {a : Ratio} {xs : List Ratio} (h : BitBound B a xs) : Bounded B a := by
  cases xs with | nil => exact h | cons b xs => exact h.1
lemma BitBound.mono {B C : ℕ} {a : Ratio} {xs : List Ratio} (h : BitBound B a xs) (hBC : B≤C) : BitBound C a xs := by
  induction xs generalizing a with
  | nil => exact ⟨h.1.trans hBC,h.2.trans hBC⟩
  | cons b xs ih => exact ⟨⟨h.1.1.trans hBC,h.1.2.trans hBC⟩,⟨h.2.1.1.trans hBC,h.2.1.2.trans hBC⟩,ih h.2.2⟩
lemma BitBound.append_transfer {B : ℕ} {a : Ratio} {xs ys : List Ratio}
    (h : BitBound B a (xs++ys)) : BitBound B (run a xs) ys := by
  induction xs generalizing a with
  | nil => exact h
  | cons b xs ih => exact ih h.2.2
lemma BitBound.prefix {B : ℕ} {a : Ratio} {xs ys : List Ratio}
    (h : BitBound B a (xs++ys)) : BitBound B a xs := by
  induction xs generalizing a with
  | nil => exact h.head
  | cons b xs ih => exact ⟨h.1,h.2.1,ih h.2.2⟩
lemma BitBound.take_transfer {B : ℕ} {a : Ratio} {xs : List Ratio} (h : BitBound B a xs) (n : ℕ) :
    BitBound B (run a (xs.take n)) (xs.drop n) := by
  apply BitBound.append_transfer
  simpa only [List.take_append_drop] using h
lemma BitBound.drop_step {B : ℕ} {a : Ratio} {xs ys : List Ratio} {i : ℕ}
    (h : BitBound B a (xs.drop i++ys)) (hi : i<xs.length) :
    Bounded B (xs[i]?.getD (0,1)) ∧ BitBound B (step a (xs[i]?.getD (0,1))) (xs.drop (i+1)++ys) := by
  rw [List.drop_eq_getElem_cons hi,List.cons_append] at h
  simpa only [List.getElem?_eq_getElem hi,Option.getD_some] using h.2

lemma step_abs_bound {A E : ℕ} {a b : Ratio}
    (ha : a.1.natAbs≤2^A ∧ a.2.natAbs≤2^A)
    (hb : b.1.natAbs≤2^E ∧ b.2.natAbs≤2^E) :
    (step a b).1.natAbs≤2^(A+E+1) ∧ (step a b).2.natAbs≤2^(A+E+1) := by
  have h1 : (a.1*b.2).natAbs≤2^(A+E) := by simpa only [Int.natAbs_mul,pow_add] using Nat.mul_le_mul ha.1 hb.2
  have h2 : (b.1*a.2).natAbs≤2^(A+E) := by simpa only [Int.natAbs_mul,pow_add,Nat.mul_comm] using Nat.mul_le_mul hb.1 ha.2
  constructor
  · exact (Int.natAbs_add_le _ _).trans (by simpa [pow_succ,mul_two] using Nat.add_le_add h1 h2)
  · apply (show (a.2*b.2).natAbs≤2^(A+E) by simpa only [Int.natAbs_mul,pow_add] using Nat.mul_le_mul ha.2 hb.2).trans
    exact Nat.pow_le_pow_right (by decide) (by omega)

lemma bitBound_of_abs (a : Ratio) (xs : List Ratio) (A E : ℕ)
    (ha : a.1.natAbs≤2^A ∧ a.2.natAbs≤2^A)
    (hs : ∀b∈xs,b.1.natAbs≤2^E ∧ b.2.natAbs≤2^E) :
    BitBound (A+(E+1)*xs.length+E+2) a xs := by
  induction xs generalizing a A with
  | nil =>
    exact ⟨(signedBits_length_of_abs_bound ha.1).trans (by simp),
      (signedBits_length_of_abs_bound ha.2).trans (by simp)⟩
  | cons b xs ih =>
    have hb := hs b (by simp)
    have hn := ih (step a b) (A+E+1) (step_abs_bound ha hb) (by intro z hz;exact hs z (by simp [hz]))
    refine ⟨⟨(signedBits_length_of_abs_bound ha.1).trans ?_,(signedBits_length_of_abs_bound ha.2).trans ?_⟩,
      ⟨(signedBits_length_of_abs_bound hb.1).trans ?_,(signedBits_length_of_abs_bound hb.2).trans ?_⟩,?_⟩
    all_goals try {simp only [List.length_cons];omega}
    convert hn using 1 <;> simp only [List.length_cons] <;> ring

end HiddenCircuits.Complexity.BinaryArithmetic.RationalAccumulator
