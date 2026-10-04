import HiddenCircuits.DH.Runtime.CoefficientModel
import HiddenCircuits.Complexity.BinaryArithmetic.AccumulatorRuntime

/-! Class-independent bounds for cached nonnegative coefficient-row arithmetic.
The only size parameter is the literal input serialization plus unary n. -/
namespace HiddenCircuits.DH.Runtime.CoefficientRow
open Complexity Complexity.BinaryArithmetic CoefficientModel PruningModel
open scoped BigOperators

def rowWords (xs : List ℕ) : List BitString := xs.map (fun (a : ℕ)=>signedBits (a:ℤ))
def rowBits (xs : List ℕ) : BitString := encodeBitList (HiddenCircuits.DH.Runtime.CoefficientRow.rowWords xs)
def inputSize (n : ℕ) (left right : List ℕ) : ℕ := n+(rowBits left).length+(rowBits right).length+1

def termExponent (S : ℕ) : ℕ := 2*S+2*S*S
def entryExponent (S : ℕ) : ℕ := termExponent S+3*(S+1)
def wordBound (S : ℕ) : ℕ := entryExponent S+2

lemma read_mem (xs : List ℕ) (i : ℕ) (hi : i<xs.length) : CoefficientModel.read xs i∈xs := by
  simp only [CoefficientModel.read,List.getElem?_eq_getElem hi,Option.getD_some]
  exact List.getElem_mem hi

lemma read_word_length (xs : List ℕ) (i : ℕ) (hi : i<xs.length) :
    (signedBits (CoefficientModel.read xs i : ℤ)).length≤(rowBits xs).length := by
  apply member_length_le_encodeBitList (xs:=HiddenCircuits.DH.Runtime.CoefficientRow.rowWords xs)
  unfold HiddenCircuits.DH.Runtime.CoefficientRow.rowWords
  exact List.mem_map.mpr ⟨CoefficientModel.read xs i,read_mem xs i hi,rfl⟩

lemma read_bound (xs : List ℕ) (i S : ℕ) (hS : (rowBits xs).length≤S) : CoefficientModel.read xs i≤2^S := by
  by_cases hi : i<xs.length
  · have h := abs_le_pow_signed_length (CoefficientModel.read xs i : ℤ) S ((read_word_length xs i hi).trans hS)
    exact h
  · simp [CoefficientModel.read,List.getElem?_eq_none (by omega),hi]

lemma index_pow_bound (S i j : ℕ) (hi : i≤S) (hj : j≤S) : i^j≤2^(S*S) := by
  have hbase : i≤2^S := hi.trans (Nat.lt_two_pow_self (n:=S)).le
  calc
    i^j ≤ (2^S)^j := Nat.pow_le_pow_left hbase j
    _ ≤ (2^S)^S := Nat.pow_le_pow_right (by positivity) hj
    _ = 2^(S*S) := (pow_mul 2 S S).symm

lemma factorial_bound (S i : ℕ) (hi : i≤S) : i.factorial≤2^(S*S) :=
  (Nat.factorial_le_pow i).trans (index_pow_bound S i i hi hi)

lemma cross_bound (S i j r : ℕ) (hi : i≤S) (hj : j≤S) :
    i.choose r*j.choose r*r.factorial≤2^(2*S*S) := by
  by_cases hri : r ≤ i
  · by_cases hrj : r ≤ j
    · rw [←crossing_division i j r hri hrj]
      calc
        _ ≤ i.factorial*j.factorial := Nat.div_le_self _ _
        _ ≤ 2^(S*S)*2^(S*S) := Nat.mul_le_mul (factorial_bound S i hi) (factorial_bound S j hj)
        _ = 2^(2*S*S) := by rw [←pow_add];congr 1;ring
    · rw [Nat.choose_eq_zero_of_lt (by omega : j<r)]
      simp
  · rw [Nat.choose_eq_zero_of_lt (by omega : i<r)]
    simp

lemma descending_bound (S i j : ℕ) (hi : i≤S) (hj : j≤S) : i.descFactorial j≤2^(2*S*S) := by
  apply (Nat.descFactorial_le_pow i j).trans ((index_pow_bound S i j hi hj).trans ?_)
  exact Nat.pow_le_pow_right (by decide) (by nlinarith)

lemma product_term_bound (S A B : ℕ) (hA : A≤2^S) (hB : B≤2^S) : A*B≤2^(termExponent S) := by
  calc
    A*B ≤ 2^S*2^S := Nat.mul_le_mul hA hB
    _ = 2^(S+S) := (pow_add 2 S S).symm
    _ ≤ 2^(termExponent S) := Nat.pow_le_pow_right (by decide) (by unfold termExponent;omega)

lemma cross_term_bound (S A B i j r : ℕ) (hA : A≤2^S) (hB : B≤2^S) (hi : i≤S) (hj : j≤S) :
    A*B*(i.choose r*j.choose r*r.factorial)≤2^(termExponent S) := by
  calc
    _ ≤ (2^S*2^S)*2^(2*S*S) := Nat.mul_le_mul (Nat.mul_le_mul hA hB) (cross_bound S i j r hi hj)
    _ = 2^(termExponent S) := by simp only [←pow_add];congr 1;unfold termExponent;omega

lemma pendant_term_bound (S A B i j : ℕ) (hA : A≤2^S) (hB : B≤2^S) (hi : i≤S) (hj : j≤S) :
    A*B*i.descFactorial j≤2^(termExponent S) := by
  calc
    _ ≤ (2^S*2^S)*2^(2*S*S) := Nat.mul_le_mul (Nat.mul_le_mul hA hB) (descending_bound S i j hi hj)
    _ = 2^(termExponent S) := by simp only [←pow_add];congr 1;unfold termExponent;omega

/-- One actual bounded-index sum increases the exponent by at most S+1. -/
lemma sum_range_bound (S E m : ℕ) (hm : m≤S+1) (f : ℕ→ℕ)
    (hf : ∀i∈Finset.range m, f i≤2^E) :
    (∑i∈Finset.range m, f i)≤2^(E+(S+1)) := by
  calc
    _ ≤ ∑i∈Finset.range m, 2^E := Finset.sum_le_sum hf
    _ = m*2^E := by simp
    _ ≤ 2^(S+1)*2^E := Nat.mul_le_mul_right _ (hm.trans (Nat.lt_two_pow_self (n:=S+1)).le)
    _ = 2^(E+(S+1)) := by rw [←pow_add];congr 1;ring

/-- Every complete row entry is bounded directly from the serialized inputs,
without any bag, graph-class, or intermediate execution assumption. -/
theorem mergeEntry_bound (n : ℕ) (kind : Kind) (a b : ℕ) (left right : List ℕ) (k : ℕ)
    (ha : a≤n) (hb : b≤n) (hk : k≤n) :
    mergeEntry kind a b left right k≤2^(entryExponent (inputSize n left right)) := by
  let S := inputSize n left right
  change mergeEntry kind a b left right k≤2^(entryExponent S)
  have hn : n≤S := by unfold S inputSize;omega
  have hL (i : ℕ) : CoefficientModel.read left i≤2^S := read_bound left i S (by unfold S inputSize;omega)
  have hR (i : ℕ) : CoefficientModel.read right i≤2^S := read_bound right i S (by unfold S inputSize;omega)
  cases kind with
  | twin joined =>
    cases joined with
    | false =>
      apply (sum_range_bound S (termExponent S) (k+1) (by omega)
        (fun i=>CoefficientModel.read left i*CoefficientModel.read right (k-i)) (fun i _=>product_term_bound S _ _ (hL i) (hR (k-i)))).trans
      exact Nat.pow_le_pow_right (by decide) (by unfold entryExponent;omega)
    | true =>
      rw [show entryExponent S=((termExponent S+(S+1))+(S+1))+(S+1) by unfold entryExponent;omega]
      apply sum_range_bound S ((termExponent S+(S+1))+(S+1)) (a+1) (by omega)
      intro i hi
      apply sum_range_bound S (termExponent S+(S+1)) (b+1) (by omega)
      intro j hj
      apply sum_range_bound S (termExponent S) (a+1) (by omega)
      intro r hr
      by_cases he : i+j=k+2*r
      · simp only [he,if_pos]
        exact cross_term_bound S _ _ i j r (hL i) (hR j)
          (by have := Finset.mem_range.mp hi;omega) (by have := Finset.mem_range.mp hj;omega)
      · simp only [he,if_neg];exact Nat.zero_le _
  | pendant =>
    have hsum : mergeEntry .pendant a b left right k≤2^((termExponent S+(S+1))+(S+1)) := by
      apply sum_range_bound S (termExponent S+(S+1)) (a+1) (by omega)
      intro i hi
      apply sum_range_bound S (termExponent S) (b+1) (by omega)
      intro j hj
      by_cases he : i=k+j
      · simp only [if_pos he]
        exact pendant_term_bound S _ _ i j (hL i) (hR j)
          (by have := Finset.mem_range.mp hi;omega) (by have := Finset.mem_range.mp hj;omega)
      · simp only [he,if_neg];exact Nat.zero_le _
    exact hsum.trans (Nat.pow_le_pow_right (by decide) (by unfold entryExponent;omega))

lemma mergeEntry_word_length (n : ℕ) (kind : Kind) (a b : ℕ) (left right : List ℕ) (k : ℕ)
    (ha : a≤n) (hb : b≤n) (hk : k≤n) :
    (signedBits (mergeEntry kind a b left right k : ℤ)).length≤wordBound (inputSize n left right) := by
  exact signedBits_length_of_abs_bound (mergeEntry_bound n kind a b left right k ha hb hk)

end HiddenCircuits.DH.Runtime.CoefficientRow
