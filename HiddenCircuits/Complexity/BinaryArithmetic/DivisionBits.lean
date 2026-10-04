import HiddenCircuits.Complexity.BinaryArithmetic.MultiplicationBits

/-! Exact binary long division. The natural-number arithmetic below specifies
loop invariants only; the finite machine implementation uses bit blocks. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic

/-- Append a bit to the low end while retaining the canonical zero word. -/
def shiftBit (xs : BitString) (b : Bool) : BitString := if b then true::xs else doubleBits xs

@[simp] theorem value_shiftBit (xs : BitString) (b : Bool) :
    value (shiftBit xs b) = 2*value xs+bitVal b := by
  cases b <;> simp [shiftBit,bitVal]; omega

theorem canonical_shiftBit {xs : BitString} (h : Canonical xs) (b : Bool) : Canonical (shiftBit xs b) := by
  cases b
  · exact canonical_doubleBits h
  · exact ⟨h,fun _ => rfl⟩

theorem length_shiftBit (xs : BitString) (b : Bool) : (shiftBit xs b).length ≤ xs.length+1 := by
  cases b
  · exact length_doubleBits xs
  · rfl

theorem canonical_length_mono {xs ys : BitString} (hx : Canonical xs) (hy : Canonical ys)
    (h : value xs ≤ value ys) : xs.length ≤ ys.length := by
  rw [canonical_eq_encode hx,canonical_eq_encode hy,encodeNat_length,encodeNat_length]
  exact Nat.size_le_size h

/-- Remainder first, quotient second. A single comparison and subtraction
suffice because the old remainder is strictly below the divisor. -/
def divStepNat (d r q : ℕ) (b : Bool) : ℕ × ℕ :=
  if 2*r+bitVal b < d then (2*r+bitVal b,2*q) else (2*r+bitVal b-d,2*q+1)

theorem divStepNat_remainder (d r q : ℕ) (b : Bool) (hr : r < d) : (divStepNat d r q b).1 < d := by
  have hb : bitVal b ≤ 1 := by cases b <;> decide
  unfold divStepNat
  split <;> simp only
  · assumption
  · omega

theorem divStepNat_equation (d r q : ℕ) (b : Bool) :
    (divStepNat d r q b).2*d+(divStepNat d r q b).1 = 2*(q*d+r)+bitVal b := by
  unfold divStepNat
  split
  · simp only; ring
  · rename_i h
    have hd : d ≤ 2*r+bitVal b := Nat.le_of_not_gt h
    have he := Nat.sub_add_cancel hd
    simp only
    nlinarith

def divFoldNat (d : ℕ) : BitString → ℕ → ℕ → ℕ × ℕ
  | [], r, q => (r,q)
  | b::bs, r, q => let rq := divStepNat d r q b; divFoldNat d bs rq.1 rq.2

theorem divFoldNat_remainder (d : ℕ) (bits : BitString) (r q : ℕ) (hr : r < d) :
    (divFoldNat d bits r q).1 < d := by
  induction bits generalizing r q with
  | nil => exact hr
  | cons b bs ih => exact ih _ _ (divStepNat_remainder d r q b hr)

theorem divFoldNat_equation (d : ℕ) (bits : BitString) (r q : ℕ) :
    (divFoldNat d bits r q).2*d+(divFoldNat d bits r q).1 =
      2^bits.length*(q*d+r)+value bits.reverse := by
  induction bits generalizing r q with
  | nil => simp [divFoldNat]
  | cons b bs ih =>
    simp only [divFoldNat,ih,divStepNat_equation,List.length_cons,pow_succ,List.reverse_cons,
      value_append,List.length_reverse,value_cons,value_nil,Nat.mul_zero,Nat.add_zero]
    ring

/-- The loop computes the ordinary Euclidean quotient and remainder. -/
theorem divFoldNat_correct (d : ℕ) (bits : BitString) (hd : 0 < d) :
    divFoldNat d bits 0 0 = (value bits.reverse % d,value bits.reverse / d) := by
  have hr := divFoldNat_remainder d bits 0 0 hd
  have he := divFoldNat_equation d bits 0 0
  simp only [Nat.zero_mul,Nat.add_zero,Nat.mul_zero,Nat.zero_add] at he
  have hd0 : d ≠ 0 := by omega
  apply Prod.ext
  · calc
      (divFoldNat d bits 0 0).1 = ((divFoldNat d bits 0 0).2*d+(divFoldNat d bits 0 0).1)%d := by
        simp [Nat.add_mod,Nat.mod_eq_of_lt hr]
      _ = _ := congrArg (fun x => x % d) he
  · calc
      (divFoldNat d bits 0 0).2 = ((divFoldNat d bits 0 0).2*d+(divFoldNat d bits 0 0).1)/d := by
        rw [Nat.add_comm,Nat.add_mul_div_right _ _ hd,Nat.div_eq_of_lt hr,Nat.zero_add]
      _ = _ := congrArg (fun x => x / d) he

/-- Specification of the bit-word update, with subtraction provided by the
separately verified borrow program. -/
def divStepBits (d r q : BitString) (b : Bool) : BitString × BitString :=
  let v := shiftBit r b
  if value v < value d then (v,doubleBits q)
  else (Computability.encodeNat (value v-value d),true::q)

theorem divStepBits_value (d r q : BitString) (b : Bool) :
    (value (divStepBits d r q b).1,value (divStepBits d r q b).2) =
      divStepNat (value d) (value r) (value q) b := by
  unfold divStepBits divStepNat
  simp only [value_shiftBit]
  split <;> simp [bitVal] <;> omega

theorem divStepBits_canonical {d r q : BitString} (hr : Canonical r) (hq : Canonical q) (b : Bool) :
    Canonical (divStepBits d r q b).1 ∧ Canonical (divStepBits d r q b).2 := by
  unfold divStepBits
  dsimp only
  split
  · exact ⟨canonical_shiftBit hr b,canonical_doubleBits hq⟩
  · exact ⟨canonical_encodeNat _,hq,fun _ => rfl⟩

def divFoldBits (d : BitString) : BitString → BitString → BitString → BitString × BitString
  | [], r, q => (r,q)
  | b::bs, r, q => let rq := divStepBits d r q b; divFoldBits d bs rq.1 rq.2

theorem divFoldBits_value (d bits r q : BitString) :
    (value (divFoldBits d bits r q).1,value (divFoldBits d bits r q).2) =
      divFoldNat (value d) bits (value r) (value q) := by
  induction bits generalizing r q with
  | nil => rfl
  | cons b bs ih =>
    simp only [divFoldBits,ih,divFoldNat]
    have h := divStepBits_value d r q b
    rw [← h]

theorem divFoldBits_canonical {d r q : BitString} (hr : Canonical r) (hq : Canonical q) (bits : BitString) :
    Canonical (divFoldBits d bits r q).1 ∧ Canonical (divFoldBits d bits r q).2 := by
  induction bits generalizing r q with
  | nil => exact ⟨hr,hq⟩
  | cons b bs ih =>
    obtain ⟨hr',hq'⟩ := divStepBits_canonical (d := d) hr hq b
    exact ih hr' hq'

@[simp] theorem divFoldBits_encodeNat (m n : ℕ) (hn : 0 < n) :
    divFoldBits (Computability.encodeNat n) (Computability.encodeNat m).reverse [] [] =
      (Computability.encodeNat (m%n),Computability.encodeNat (m/n)) := by
  have hv := divFoldBits_value (Computability.encodeNat n) (Computability.encodeNat m).reverse [] []
  rw [value_encodeNat,value_nil,divFoldNat_correct _ _ hn,List.reverse_reverse,value_encodeNat] at hv
  have hc := divFoldBits_canonical (d := Computability.encodeNat n) canonical_nil canonical_nil
    (Computability.encodeNat m).reverse
  apply Prod.ext
  · rw [canonical_eq_encode hc.1,show value (divFoldBits _ _ [] []).1 = m%n from congrArg Prod.fst hv]
  · rw [canonical_eq_encode hc.2,show value (divFoldBits _ _ [] []).2 = m/n from congrArg Prod.snd hv]

end HiddenCircuits.Complexity.BinaryArithmetic
