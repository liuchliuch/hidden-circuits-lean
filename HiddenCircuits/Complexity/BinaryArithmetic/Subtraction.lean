import HiddenCircuits.Complexity.BinaryArithmetic.Bits

/-! Exact borrow arithmetic and canonical binary subtraction. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic

def borrowBit (a b c : Bool) : Bool := ((!a) && (b || c)) || (b && c)

theorem fullSubtractor_value (a b c : Bool) :
    bitVal a+2*bitVal (borrowBit a b c)=bitVal b+bitVal c+bitVal (sumBit a b c) := by
  cases a <;> cases b <;> cases c <;> rfl

def subRaw : BitString → BitString → Bool → BitString × Bool
  | [],[],c => ([],c)
  | a::as,[],c => let r := subRaw as [] (borrowBit a false c); (sumBit a false c::r.1,r.2)
  | [],b::bs,c => let r := subRaw [] bs (borrowBit false b c); (sumBit false b c::r.1,r.2)
  | a::as,b::bs,c => let r := subRaw as bs (borrowBit a b c); (sumBit a b c::r.1,r.2)

theorem subRaw_length (xs ys : BitString) (c : Bool) : (subRaw xs ys c).1.length=max xs.length ys.length := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => simp [subRaw]
    | cons b bs ih => simp [subRaw,ih]
  | cons a as ih => cases ys <;> simp [subRaw,ih,max_add_add_right]

theorem subRaw_value (xs ys : BitString) (c : Bool) :
    value xs+2^(max xs.length ys.length)*bitVal (subRaw xs ys c).2=
      value ys+bitVal c+value (subRaw xs ys c).1 := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => simp [subRaw]
    | cons b bs ih =>
      have hh := ih (borrowBit false b c)
      have hb := fullSubtractor_value false b c
      simp only [subRaw,value_cons,List.length_cons,List.length_nil,Nat.zero_max,pow_succ,value_nil] at *
      simp only [show bitVal false=0 from rfl] at hb
      nlinarith
  | cons a as ih =>
    cases ys with
    | nil =>
      have hh := ih [] (borrowBit a false c)
      have hb := fullSubtractor_value a false c
      simp only [subRaw,value_cons,List.length_cons,List.length_nil,Nat.max_zero,pow_succ,value_nil] at *
      simp only [show bitVal false=0 from rfl] at hb
      nlinarith
    | cons b bs =>
      have hh := ih bs (borrowBit a b c)
      have hb := fullSubtractor_value a b c
      simp only [subRaw,value_cons,List.length_cons,max_add_add_right,pow_succ] at *
      nlinarith

theorem value_lt_pow_length (xs : BitString) : value xs<2^xs.length := by
  induction xs with
  | nil => simp
  | cons b bs ih => cases b <;> simp [value,bitVal,pow_succ] <;> omega

theorem subRaw_borrow (xs ys : BitString) : (subRaw xs ys false).2=true ↔ value xs<value ys := by
  have hv := subRaw_value xs ys false
  have hb := value_lt_pow_length (subRaw xs ys false).1
  rw [subRaw_length] at hb
  cases he : (subRaw xs ys false).2 <;> simp [he,bitVal] at hv ⊢ <;> omega

def normalize : BitString → BitString
  | [] => []
  | b::bs => let t := normalize bs; if t=[] ∧ b=false then [] else b::t

@[simp] theorem value_normalize (xs : BitString) : value (normalize xs)=value xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    simp only [normalize]
    split_ifs with h
    · rcases h with ⟨h1,rfl⟩; simp [h1] at ih; simp [value,bitVal,←ih]
    · simp [value,ih]

theorem canonical_normalize (xs : BitString) : Canonical (normalize xs) := by
  induction xs with
  | nil => trivial
  | cons b bs ih =>
    simp only [normalize]
    split_ifs with h
    · trivial
    · refine ⟨ih,?_⟩
      intro he
      cases b
      · exact False.elim (h ⟨he,rfl⟩)
      · rfl

theorem normalize_eq_encode (xs : BitString) : normalize xs=Computability.encodeNat (value xs) := by
  simpa using canonical_eq_encode (canonical_normalize xs)

def subtractBits (xs ys : BitString) : BitString :=
  let r := subRaw xs ys false
  if r.2 then [] else normalize r.1

theorem subtractBits_correct (xs ys : BitString) :
    subtractBits xs ys=Computability.encodeNat (value xs-value ys) := by
  have hv := subRaw_value xs ys false
  have hb := subRaw_borrow xs ys
  unfold subtractBits
  cases he : (subRaw xs ys false).2
  · simp only [he,Bool.false_eq_true,ite_false,normalize_eq_encode]
    simp [he,bitVal] at hv
    congr 1
    omega
  · have hl : value xs<value ys := hb.mp he
    simp [he,Nat.sub_eq_zero_of_le hl.le,Computability.encodeNat,Computability.encodeNum]

@[simp] theorem subtract_encodeNat (x y : ℕ) :
    subtractBits (Computability.encodeNat x) (Computability.encodeNat y)=Computability.encodeNat (x-y) := by
  simpa using subtractBits_correct (Computability.encodeNat x) (Computability.encodeNat y)


@[simp] theorem normalize_append_false (xs : BitString) : normalize (xs++[false])=normalize xs := by
  induction xs with
  | nil => simp [normalize]
  | cons b xs ih => simp only [List.cons_append,normalize,ih]

@[simp] theorem normalize_append_true (xs : BitString) : normalize (xs++[true])=xs++[true] := by
  induction xs with
  | nil => simp [normalize]
  | cons b xs ih => simp [normalize,ih]

@[simp] theorem normalize_reverse_false (xs : BitString) : normalize (false::xs).reverse=normalize xs.reverse := by
  simp [List.reverse_cons]

@[simp] theorem normalize_reverse_true (xs : BitString) : normalize (true::xs).reverse=xs.reverse++[true] := by
  simp [List.reverse_cons]

end HiddenCircuits.Complexity.BinaryArithmetic
