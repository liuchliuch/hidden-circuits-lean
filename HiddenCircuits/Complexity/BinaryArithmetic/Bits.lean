import HiddenCircuits.Complexity.OracleIncrement
import HiddenCircuits.Complexity.OracleCopyProgram

/-! Little-endian arithmetic on the exact bit strings used by oracle answers. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic

abbrev bitVal (b : Bool) : ℕ := if b then 1 else 0

def value : BitString → ℕ
  | [] => 0
  | b::bs => bitVal b + 2*value bs

@[simp] theorem value_nil : value [] = 0 := rfl
@[simp] theorem value_cons (b : Bool) (bs : BitString) :
    value (b::bs) = bitVal b + 2*value bs := rfl

@[simp] theorem value_encodePosNum (n : PosNum) :
    value (Computability.encodePosNum n) = (n : ℕ) := by
  induction n <;> simp_all [Computability.encodePosNum,PosNum.cast_bit0,PosNum.cast_bit1,bitVal] <;> omega

@[simp] theorem value_encodeNum (n : Num) :
    value (Computability.encodeNum n) = (n : ℕ) := by
  cases n <;> simp [Computability.encodeNum]

@[simp] theorem value_encodeNat (n : ℕ) : value (Computability.encodeNat n) = n := by
  simp [Computability.encodeNat,Num.to_of_nat]

/-- Canonical little-endian words have no redundant most-significant zero. -/
def Canonical : BitString → Prop
  | [] => True
  | b::bs => Canonical bs ∧ (bs = [] → b = true)

@[simp] theorem canonical_nil : Canonical [] := trivial
@[simp] theorem canonical_cons (b : Bool) (bs : BitString) :
    Canonical (b::bs) ↔ Canonical bs ∧ (bs = [] → b = true) := Iff.rfl

@[simp] theorem canonical_encodePosNum (n : PosNum) :
    Canonical (Computability.encodePosNum n) := by
  induction n <;> simp_all [Computability.encodePosNum,Computability.encodePosNum_nonempty]

@[simp] theorem canonical_encodeNat (n : ℕ) : Canonical (Computability.encodeNat n) := by
  unfold Computability.encodeNat
  cases (n : Num) <;> simp [Computability.encodeNum]

theorem canonical_value_eq_zero {xs : BitString} (h : Canonical xs) :
    value xs = 0 ↔ xs = [] := by
  induction xs with
  | nil => simp
  | cons b bs ih =>
    obtain ⟨hc,hb⟩ := h
    have hi := ih hc
    cases b <;> simp_all [bitVal] <;> omega

theorem canonical_injective {xs ys : BitString} (hx : Canonical xs) (hy : Canonical ys)
    (hv : value xs = value ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => exact ((canonical_value_eq_zero hy).mp hv.symm).symm
  | cons b bs ih =>
    cases ys with
    | nil => exact (canonical_value_eq_zero hx).mp hv
    | cons c cs =>
      obtain ⟨hbs,_⟩ := hx
      obtain ⟨hcs,_⟩ := hy
      have hbc : b = c := by cases b <;> cases c <;> simp_all [bitVal] <;> omega
      subst c
      have hs : value bs = value cs := by simp only [value_cons] at hv; omega
      rw [ih hbs hcs hs]

/-- Canonicality and the usual binary value identify exactly `encodeNat`. -/
theorem canonical_eq_encode {xs : BitString} (h : Canonical xs) :
    xs = Computability.encodeNat (value xs) :=
  canonical_injective h (canonical_encodeNat _) (value_encodeNat _).symm

def sumBit (a b carry : Bool) : Bool := xor (xor a b) carry
def carryBit (a b carry : Bool) : Bool := (a && b) || (a && carry) || (b && carry)

theorem fullAdder_value (a b c : Bool) :
    bitVal (sumBit a b c) + 2*bitVal (carryBit a b c) = bitVal a+bitVal b+bitVal c := by
  cases a <;> cases b <;> cases c <;> rfl

/-- Ripple-carry addition. Each recursive call consumes at least one input bit. -/
def addBits : BitString → BitString → Bool → BitString
  | [], [], carry => if carry then [true] else []
  | a::as, [], carry => sumBit a false carry :: addBits as [] (carryBit a false carry)
  | [], b::bs, carry => sumBit false b carry :: addBits [] bs (carryBit false b carry)
  | a::as, b::bs, carry => sumBit a b carry :: addBits as bs (carryBit a b carry)

@[simp] theorem value_addBits (xs ys : BitString) (c : Bool) :
    value (addBits xs ys c) = value xs+value ys+bitVal c := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => cases c <;> simp [addBits,bitVal]
    | cons b bs ih =>
      simp only [addBits,value_cons,ih]
      have h := fullAdder_value false b c
      simp only [show bitVal false = 0 from rfl,value_nil] at *
      omega
  | cons a as ih =>
    cases ys with
    | nil =>
      simp only [addBits,value_cons,ih,value_nil]
      have h := fullAdder_value a false c
      simp only [show bitVal false = 0 from rfl,value_nil] at *
      omega
    | cons b bs =>
      simp only [addBits,value_cons,ih]
      have h := fullAdder_value a b c
      omega

theorem length_addBits (xs ys : BitString) (c : Bool) :
    (addBits xs ys c).length ≤ max xs.length ys.length+1 := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => cases c <;> simp [addBits]
    | cons b bs ih => simpa [addBits] using Nat.add_le_add_right (ih (carryBit false b c)) 1
  | cons a as ih =>
    cases ys with
    | nil => simpa [addBits] using Nat.add_le_add_right (ih [] (carryBit a false c)) 1
    | cons b bs => simpa [addBits,max_add_add_right] using
        Nat.add_le_add_right (ih bs (carryBit a b c)) 1

/-- Addition preserves the exact no-leading-zero representation. -/
theorem canonical_addBits {xs ys : BitString} (hx : Canonical xs) (hy : Canonical ys) (c : Bool) :
    Canonical (addBits xs ys c) := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => cases c <;> simp [addBits]
    | cons b bs ih =>
      obtain ⟨hbs,hb⟩ := hy
      simp only [addBits,canonical_cons]
      refine ⟨ih hbs _,?_⟩
      intro he
      have hv := value_addBits [] bs (carryBit false b c)
      rw [he] at hv
      simp only [value_nil] at hv
      have hz : value bs = 0 := by omega
      have hnil := (canonical_value_eq_zero hbs).mp hz
      have hb' := hb hnil
      subst b
      cases c
      · rfl
      · norm_num [carryBit,bitVal] at hv
  | cons a as ih =>
    obtain ⟨has,ha⟩ := hx
    cases ys with
    | nil =>
      simp only [addBits,canonical_cons]
      refine ⟨ih has canonical_nil _,?_⟩
      intro he
      have hv := value_addBits as [] (carryBit a false c)
      rw [he] at hv
      simp only [value_nil] at hv
      have hz : value as = 0 := by omega
      have hnil := (canonical_value_eq_zero has).mp hz
      have ha' := ha hnil
      subst a
      cases c
      · rfl
      · norm_num [carryBit,bitVal] at hv
    | cons b bs =>
      obtain ⟨hbs,hb⟩ := hy
      simp only [addBits,canonical_cons]
      refine ⟨ih has hbs _,?_⟩
      intro he
      have hv := value_addBits as bs (carryBit a b c)
      rw [he] at hv
      simp only [value_nil] at hv
      have hza : value as = 0 := by omega
      have hzb : value bs = 0 := by omega
      have ha' := ha ((canonical_value_eq_zero has).mp hza)
      have hb' := hb ((canonical_value_eq_zero hbs).mp hzb)
      subst a; subst b
      cases c <;> norm_num [carryBit,bitVal] at hv

@[simp] theorem addBits_encodeNat (m n : ℕ) (c : Bool) :
    addBits (Computability.encodeNat m) (Computability.encodeNat n) c =
      Computability.encodeNat (m+n+bitVal c) := by
  rw [canonical_eq_encode (canonical_addBits (canonical_encodeNat m) (canonical_encodeNat n) c)]
  simp

end HiddenCircuits.Complexity.BinaryArithmetic
