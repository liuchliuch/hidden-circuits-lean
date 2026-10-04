import HiddenCircuits.DH.Runtime.PruningModel

/-! Cached nonnegative coefficient tables for the slower binary FP program.
These literal finite sums are the mathematical refinement target of the
bit-stack loops; this module does not assume a machine-cost annotation. -/
namespace HiddenCircuits.DH.Runtime.CoefficientModel
open PruningModel
open scoped BigOperators

/-- Missing slots have the same zero convention as the verified bag arrays. -/
def read (xs : List ℕ) (i : ℕ) : ℕ := xs[i]?.getD 0

def mergeBag : Kind→BagExpr→BagExpr→BagExpr
  | .twin false,a,b => .falseTwin a b
  | .twin true,a,b => .trueTwin a b
  | .pendant,a,b => .pendant a b

def mergeEntry (kind : Kind) (a b : ℕ) (left right : List ℕ) (k : ℕ) : ℕ :=
  match kind with
  | .twin false => ∑i∈Finset.range (k+1), read left i*read right (k-i)
  | .twin true => ∑i∈Finset.range (a+1), ∑j∈Finset.range (b+1), ∑r∈Finset.range (a+1),
      if i+j=k+2*r then read left i*read right j*(i.choose r*j.choose r*r.factorial) else 0
  | .pendant => ∑i∈Finset.range (a+1), ∑j∈Finset.range (b+1),
      if i=k+j then read left i*read right j*i.descFactorial j else 0

def mergeRow (n : ℕ) (kind : Kind) (a b : ℕ) (left right : List ℕ) : List ℕ :=
  List.ofFn (fun k : Fin (n+1)=>mergeEntry kind a b left right k.val)

def leafRow (n : ℕ) : List ℕ := List.ofFn (fun k : Fin (n+1)=>if k.val=1 then 1 else 0)

def Represents (xs : List ℕ) (e : BagExpr) : Prop := ∀k, read xs k=e.state k

@[simp] lemma mergeBag_size (kind : Kind) (a b : BagExpr) : (mergeBag kind a b).size=a.size+b.size := by
  cases kind with
  | twin joined => cases joined <;> rfl
  | pendant => rfl

lemma mergeEntry_correct (kind : Kind) (a b : BagExpr) (left right : List ℕ)
    (hl : Represents left a) (hr : Represents right b) (k : ℕ) :
    mergeEntry kind a.size b.size left right k=(mergeBag kind a b).state k := by
  unfold Represents at hl hr
  cases kind with
  | twin joined =>
      cases joined <;> simp only [mergeEntry,mergeBag,BagExpr.state,←Fin.sum_univ_eq_sum_range,hl,hr]
  | pendant => simp only [mergeEntry,mergeBag,BagExpr.state,←Fin.sum_univ_eq_sum_range,hl,hr]

lemma leafRow_represents (n : ℕ) (hn : 1≤n) : Represents (leafRow n) .leaf := by
  intro k
  by_cases hk : k<n+1
  · simp only [read,leafRow,List.getElem?_ofFn,hk,↓reduceDIte,Option.getD_some,BagExpr.state]
  · have hk1 : k≠1 := by omega
    simp [read,leafRow,hk,BagExpr.state,hk1]

lemma mergeRow_represents (n : ℕ) (kind : Kind) (a b : BagExpr) (left right : List ℕ)
    (hl : Represents left a) (hr : Represents right b) (hsize : a.size+b.size≤n) :
    Represents (mergeRow n kind a.size b.size left right) (mergeBag kind a b) := by
  intro k
  by_cases hk : k<n+1
  · simp only [read,mergeRow,List.getElem?_ofFn,hk,↓reduceDIte,Option.getD_some]
    exact mergeEntry_correct kind a b left right hl hr k
  · have hz := BagExpr.state_zero_of_size_lt (mergeBag kind a b) k (by rw [mergeBag_size];omega)
    simp [read,mergeRow,hk,hz]

@[simp] lemma leafRow_length (n : ℕ) : (leafRow n).length=n+1 := by simp [leafRow]
@[simp] lemma mergeRow_length (n : ℕ) (kind : Kind) (a b : ℕ) (left right : List ℕ) :
    (mergeRow n kind a b left right).length=n+1 := by simp [mergeRow]

/-- The exponent is polynomial in n, sufficient for a literal polynomial bit
runtime without relying on an unproved arithmetic instruction cost. -/
lemma state_bound_pow_two (e : BagExpr) (n k : ℕ) (hn : e.size≤n) :
    e.state k≤2^((n+1)^2) := by
  have hs := e.state_bound k
  have h1 : e.size+1≤2^(n+1) := (Nat.add_le_add_right hn 1).trans (Nat.le_of_lt (show n+1<2^(n+1) from Nat.lt_two_pow_self))
  have h2 : (e.size+1)^e.size≤(2^(n+1))^n :=
    (Nat.pow_le_pow_left h1 _).trans (Nat.pow_le_pow_right (by positivity) hn)
  have hexp : (n+1)*n≤(n+1)^2 := by nlinarith
  apply hs.trans (h2.trans ?_)
  rw [←pow_mul]
  exact Nat.pow_le_pow_right (by decide) hexp

lemma row_bound (xs : List ℕ) (e : BagExpr) (n : ℕ) (h : Represents xs e) (hn : e.size≤n) :
    ∀k, read xs k≤2^((n+1)^2) := by
  intro k
  rw [h k]
  exact state_bound_pow_two e n k hn

/-- Exact factorial quotient for the crossing-endpoint multiplicity. The
runtime can use the already verified factorial/multiply/divide bit blocks. -/
lemma crossing_factorial (i j r : ℕ) (hri : r ≤ i) (hrj : r ≤ j) :
    (i.choose r*j.choose r*r.factorial) * (r.factorial*(i-r).factorial*(j-r).factorial) =
      i.factorial*j.factorial := by
  have hi := Nat.choose_mul_factorial_mul_factorial hri
  have hj := Nat.choose_mul_factorial_mul_factorial hrj
  calc
    _ = (i.choose r*r.factorial*(i-r).factorial)*(j.choose r*r.factorial*(j-r).factorial) := by ring
    _ = _ := by rw [hi,hj]

lemma crossing_division (i j r : ℕ) (hri : r ≤ i) (hrj : r ≤ j) :
    (i.factorial*j.factorial)/(r.factorial*(i-r).factorial*(j-r).factorial) =
      i.choose r*j.choose r*r.factorial := by
  rw [←crossing_factorial i j r hri hrj]
  exact Nat.mul_div_cancel _ (by positivity)

end HiddenCircuits.DH.Runtime.CoefficientModel
