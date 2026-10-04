import HiddenCircuits.Complexity.BinaryArithmetic.Bits

namespace HiddenCircuits.Complexity.BinaryArithmetic

/-- Multiplication by two, preserving the empty representation of zero. -/
def doubleBits : BitString → BitString
  | [] => []
  | b::bs => false::b::bs

@[simp] theorem value_doubleBits (xs : BitString) : value (doubleBits xs) = 2*value xs := by
  cases xs <;> simp [doubleBits,bitVal]

theorem length_doubleBits (xs : BitString) : (doubleBits xs).length ≤ xs.length+1 := by
  cases xs <;> simp [doubleBits]

theorem canonical_doubleBits {xs : BitString} (h : Canonical xs) : Canonical (doubleBits xs) := by
  cases xs <;> simpa [doubleBits] using h

@[simp] theorem doubleBits_encodeNat (n : ℕ) :
    doubleBits (Computability.encodeNat n) = Computability.encodeNat (2*n) := by
  rw [canonical_eq_encode (canonical_doubleBits (canonical_encodeNat n))]
  simp

@[simp] theorem value_append (xs ys : BitString) :
    value (xs++ys) = value xs+2^xs.length*value ys := by
  induction xs with
  | nil => simp
  | cons b bs ih => simp [ih,pow_succ]; ring

def mulStep (ys acc : BitString) (b : Bool) : BitString :=
  if b then addBits (doubleBits acc) ys false else doubleBits acc

@[simp] theorem value_mulStep (ys acc : BitString) (b : Bool) :
    value (mulStep ys acc b) = 2*value acc+bitVal b*value ys := by
  cases b <;> simp [mulStep,bitVal]

theorem canonical_mulStep {ys acc : BitString} (hy : Canonical ys) (ha : Canonical acc) (b : Bool) :
    Canonical (mulStep ys acc b) := by
  cases b
  · exact canonical_doubleBits ha
  · exact canonical_addBits (canonical_doubleBits ha) hy false

theorem length_mulStep (ys acc : BitString) (b : Bool) :
    (mulStep ys acc b).length ≤ acc.length+ys.length+2 := by
  have hd := length_doubleBits acc
  cases b
  · simpa [mulStep] using hd.trans (by omega : acc.length+1 ≤ acc.length+ys.length+2)
  · have h := length_addBits (doubleBits acc) ys false
    simp only [mulStep,ite_true]
    omega

/-- Most-significant-first Horner evaluation, each step consisting of a binary
shift and at most one ripple-carry addition. -/
def mulFold (ys : BitString) : BitString → BitString → BitString
  | [], acc => acc
  | b::bs, acc => mulFold ys bs (mulStep ys acc b)

@[simp] theorem value_mulFold (ys bits acc : BitString) :
    value (mulFold ys bits acc) = 2^bits.length*value acc+value bits.reverse*value ys := by
  induction bits generalizing acc with
  | nil => simp [mulFold]
  | cons b bs ih =>
    simp only [mulFold,ih,value_mulStep,List.length_cons,pow_succ,List.reverse_cons,value_append,
      List.length_reverse,value_cons,value_nil,Nat.mul_zero,Nat.add_zero]
    ring

theorem canonical_mulFold {ys acc : BitString} (hy : Canonical ys) (ha : Canonical acc) (bits : BitString) :
    Canonical (mulFold ys bits acc) := by
  induction bits generalizing acc with
  | nil => exact ha
  | cons b bs ih => exact ih (canonical_mulStep hy ha b)

theorem length_mulFold (ys bits acc : BitString) :
    (mulFold ys bits acc).length ≤ acc.length+bits.length*(ys.length+2) := by
  induction bits generalizing acc with
  | nil => simp [mulFold]
  | cons b bs ih =>
    have h := ih (mulStep ys acc b)
    have hs := length_mulStep ys acc b
    simp only [mulFold,List.length_cons]
    nlinarith

def mulBits (xs ys : BitString) : BitString := mulFold ys xs.reverse []

@[simp] theorem value_mulBits (xs ys : BitString) : value (mulBits xs ys) = value xs*value ys := by
  simp [mulBits]

@[simp] theorem mulBits_encodeNat (m n : ℕ) :
    mulBits (Computability.encodeNat m) (Computability.encodeNat n) = Computability.encodeNat (m*n) := by
  have hc : Canonical (mulBits (Computability.encodeNat m) (Computability.encodeNat n)) :=
    canonical_mulFold (canonical_encodeNat n) canonical_nil _
  rw [canonical_eq_encode hc]
  simp

end HiddenCircuits.Complexity.BinaryArithmetic
