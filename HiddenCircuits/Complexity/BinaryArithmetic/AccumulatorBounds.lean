import HiddenCircuits.Complexity.BinaryArithmetic.AccumulatorSum

/-! Discharge accumulator bit invariants from ordinary integer magnitude bounds.
These lemmas connect the real arithmetic loops to interpolation envelopes. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic

lemma signedBits_length_of_abs_bound {z : ℤ} {E : ℕ} (h : z.natAbs≤2^E) :
    (signedBits z).length≤E+2 := by
  have hs := Nat.size_le_size h
  simpa [signedBits,encodeNat_length,Nat.size_pow] using Nat.add_le_add_right hs 1

theorem ProductBitBound.mono {B C : ℕ} {a : ℤ} {zs : List ℤ}
    (h : ProductBitBound B a zs) (hBC : B≤C) : ProductBitBound C a zs := by
  induction zs generalizing a with
  | nil => exact h.trans hBC
  | cons z zs ih => exact ⟨h.1.trans hBC,h.2.1.trans hBC,ih h.2.2⟩

theorem SumBitBound.mono {B C : ℕ} {a : ℤ} {zs : List ℤ}
    (h : SumBitBound B a zs) (hBC : B≤C) : SumBitBound C a zs := by
  induction zs generalizing a with
  | nil => exact h.trans hBC
  | cons z zs ih => exact ⟨h.1.trans hBC,h.2.1.trans hBC,ih h.2.2⟩

/-- No separate intermediate-bound hypothesis is needed for a product of
bounded integers: the bound follows from the input magnitudes themselves. -/
theorem productBitBound_of_abs (A B : ℕ) (a : ℤ) (zs : List ℤ)
    (ha : a.natAbs≤2^A) (hz : ∀ z∈zs, z.natAbs≤2^B) :
    ProductBitBound (A+B*zs.length+2) a zs := by
  induction zs generalizing A a with
  | nil => simpa [ProductBitBound] using signedBits_length_of_abs_bound ha
  | cons z zs ih =>
    have hz₀ := hz z (by simp)
    have hm : (a*z).natAbs≤2^(A+B) := by
      simpa [Int.natAbs_mul,pow_add] using Nat.mul_le_mul ha hz₀
    have hi := ih (A+B) (a*z) hm (fun w hw => hz w (by simp [hw]))
    refine ⟨(signedBits_length_of_abs_bound ha).trans ?_,(signedBits_length_of_abs_bound hz₀).trans ?_,?_⟩
    · simp only [List.length_cons]; nlinarith
    · simp only [List.length_cons]; nlinarith
    · convert hi using 1 <;> simp only [List.length_cons] <;> congr 1 <;> ring

lemma add_abs_envelope (A B : ℕ) (a z : ℤ) (ha : a.natAbs≤2^A) (hz : z.natAbs≤2^B) :
    (a+z).natAbs≤2^(A+B+1) := by
  calc
    _ ≤ a.natAbs+z.natAbs := Int.natAbs_add_le a z
    _ ≤ 2^A+2^B := Nat.add_le_add ha hz
    _ ≤ 2^(A+B)+2^(A+B) := Nat.add_le_add
      (Nat.pow_le_pow_right (by decide) (by omega))
      (Nat.pow_le_pow_right (by decide) (by omega))
    _ = _ := by rw [pow_succ]; omega

/-- A polynomially growing explicit envelope for every partial signed sum. -/
theorem sumBitBound_of_abs (A B : ℕ) (a : ℤ) (zs : List ℤ)
    (ha : a.natAbs≤2^A) (hz : ∀ z∈zs, z.natAbs≤2^B) :
    SumBitBound (A+(B+1)*zs.length+2) a zs := by
  induction zs generalizing A a with
  | nil => simpa [SumBitBound] using signedBits_length_of_abs_bound ha
  | cons z zs ih =>
    have hz₀ := hz z (by simp)
    have hm := add_abs_envelope A B a z ha hz₀
    have hi := ih (A+B+1) (a+z) hm (fun w hw => hz w (by simp [hw]))
    refine ⟨(signedBits_length_of_abs_bound ha).trans ?_,(signedBits_length_of_abs_bound hz₀).trans ?_,?_⟩
    · simp only [List.length_cons]; nlinarith
    · simp only [List.length_cons]; nlinarith
    · convert hi using 1 <;> simp only [List.length_cons] <;> congr 1 <;> ring

lemma foldl_mul_eq (zs : List ℤ) (a : ℤ) : zs.foldl (·*·) a = a*zs.prod := by
  induction zs generalizing a with
  | nil => simp
  | cons z zs ih => simp [List.foldl_cons,ih,mul_assoc]

lemma foldl_add_eq (zs : List ℤ) (a : ℤ) : zs.foldl (·+·) a = a+zs.sum := by
  induction zs generalizing a with
  | nil => simp
  | cons z zs ih => simp [List.foldl_cons,ih,add_assoc]

/-- Operational product with its bit invariant discharged by input bounds. -/
theorem productAccumulator_bounded (g : BitString → ℕ) (zs : List ℤ) (a : ℤ) (A B : ℕ)
    (ha : a.natAbs≤2^A) (hz : ∀ z∈zs, z.natAbs≤2^B) :
    ∃ t, productAccumulator.Executes g
      (productStore (signedBits a) [] [] [] [] [] (encodeBitList (zs.map signedBits)))
      (productStore (signedBits (a*zs.prod)) [] [] [] [] [] []) t ∧
      t≤1+zs.length*productIterationBound (A+B*zs.length+2) := by
  simpa [foldl_mul_eq] using productAccumulator_executes g zs a _ (productBitBound_of_abs A B a zs ha hz)

/-- Operational sum with its bit invariant discharged by input bounds. -/
theorem sumAccumulator_bounded (g : BitString → ℕ) (zs : List ℤ) (a : ℤ) (A B : ℕ)
    (ha : a.natAbs≤2^A) (hz : ∀ z∈zs, z.natAbs≤2^B) :
    ∃ t, sumAccumulator.Executes g
      (sumStore (signedBits a) [] [] [] (encodeBitList (zs.map signedBits)))
      (sumStore (signedBits (a+zs.sum)) [] [] [] []) t ∧
      t≤1+zs.length*sumIterationBound (A+(B+1)*zs.length+2) := by
  simpa [foldl_add_eq] using sumAccumulator_executes g zs a _ (sumBitBound_of_abs A B a zs ha hz)

end HiddenCircuits.Complexity.BinaryArithmetic
