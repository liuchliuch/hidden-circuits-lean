import HiddenCircuits.DH.Runtime.CoefficientRowBounds

/-! Fresh reconstruction: one rectangular, nonnegative three-index sum for all
three DH merge rules, with the exact lexicographic accumulator invariant. -/
namespace HiddenCircuits.DH.Runtime.UniformCoefficientModel
open PruningModel CoefficientModel
open scoped BigOperators

def test (kind : Kind) (i j r k : ℕ) : Prop :=
  match kind with
  | .twin false => r=0 ∧ i+j=k
  | .twin true => i+j=k+2*r
  | .pendant => r=j ∧ i=k+j
instance (kind : Kind) (i j r k : ℕ) : Decidable (test kind i j r k) := by
  cases kind with
  | twin b => cases b <;> unfold test <;> infer_instance
  | pendant => unfold test;infer_instance

def contribution (kind : Kind) (left right : List ℕ) (k i j r : ℕ) : ℕ :=
  if test kind i j r k then read left i*read right j*(i.choose r*j.choose r*r.factorial) else 0

def entry (kind : Kind) (a b : ℕ) (left right : List ℕ) (k : ℕ) : ℕ :=
  ∑i∈Finset.range (a+1),∑j∈Finset.range (b+1),∑r∈Finset.range (a+1),contribution kind left right k i j r

lemma false_inner (a i j k : ℕ) (left right : List ℕ) :
    (∑r∈Finset.range (a+1),contribution (.twin false) left right k i j r)=
      if i+j=k then read left i*read right j else 0 := by
  rw [Finset.sum_eq_single 0]
  · simp [contribution,test]
  · intro r hr hn;simp [contribution,test,hn]
  · simp
lemma pendant_inner (a i j k : ℕ) (hi : i ≤ a) (left right : List ℕ) :
    (∑r∈Finset.range (a+1),contribution .pendant left right k i j r)=
      if i=k+j then read left i*read right j*i.descFactorial j else 0 := by
  by_cases he:i=k+j
  · have hj : j < a+1 := by omega
    rw [Finset.sum_eq_single j]
    · simp only [contribution,test,eq_self_iff_true,true_and,if_pos he,
        Nat.choose_self,Nat.mul_one,Nat.descFactorial_eq_factorial_mul_choose]
      ring
    · intro r hr hn;simp [contribution,test,hn]
    · intro hjnot
      exact (hjnot (Finset.mem_range.mpr hj)).elim
  · simp [contribution,test,he]

lemma convolution_inner (b i k A : ℕ) (f : ℕ → ℕ) (hf : ∀j,b < j → f j=0) :
    (∑j∈Finset.range (b+1),if i+j=k then A*f j else 0)=if i ≤ k then A*f (k-i) else 0 := by
  by_cases hi:i ≤ k
  · rw [if_pos hi]
    by_cases hj:k-i ≤ b
    · rw [Finset.sum_eq_single (k-i)]
      · simp [Nat.add_sub_of_le hi]
      · intro j hmem hne
        have he : i+j≠k := by omega
        simp [he]
      · simp [Finset.mem_range,show k-i < b+1 by omega]
    · rw [hf (k-i) (by omega),Nat.mul_zero]
      apply Finset.sum_eq_zero
      intro j hmem
      have hh := Finset.mem_range.mp hmem
      have he : i+j≠k := by omega
      simp [he]
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro j hmem
    have he : i+j≠k := by omega
    simp [he]

lemma convolution_outer (a k : ℕ) (f g : ℕ → ℕ) (hf : ∀i,a < i → f i=0) :
    (∑i∈Finset.range (a+1),if i ≤ k then f i*g (k-i) else 0)=
      ∑i∈Finset.range (k+1),f i*g (k-i) := by
  by_cases hak:a ≤ k
  · calc
      _=∑i∈Finset.range (a+1),f i*g (k-i) := by
        apply Finset.sum_congr rfl
        intro i hi
        have := Finset.mem_range.mp hi
        exact if_pos (by omega)
      _=_ := Finset.sum_subset (Finset.range_mono (by omega)) (by
        intro i hi hnot
        have hin : a < i := by simpa only [Finset.mem_range,not_lt] using hnot
        simp [hf i hin])
  · have hsum := Finset.sum_subset (Finset.range_mono (show k+1 ≤ a+1 by omega))
      (f:=fun i => if i ≤ k then f i*g (k-i) else 0) (by
        intro i hi hnot
        have hin : ¬i ≤ k := by have := hnot;simp only [Finset.mem_range] at this;omega
        simp [hin])
    rw [←hsum]
    apply Finset.sum_congr rfl
    intro i hi
    have := Finset.mem_range.mp hi
    dsimp only
    exact if_pos (by omega)

theorem entry_eq_mergeEntry (kind : Kind) (a b : ℕ) (left right : List ℕ) (k : ℕ)
    (hl : ∀i,a < i → read left i=0) (hr : ∀j,b < j → read right j=0) :
    entry kind a b left right k=mergeEntry kind a b left right k := by
  cases kind with
  | twin joined =>
    cases joined with
    | false =>
      simp only [entry,false_inner,mergeEntry]
      simp_rw [convolution_inner b _ k _ (read right) hr]
      exact convolution_outer a k (read left) (read right) hl
    | true => rfl
  | pendant =>
    unfold entry mergeEntry
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact pendant_inner a i j k (by have := Finset.mem_range.mp hi;omega) left right

theorem represented_entry (kind : Kind) (a b : BagExpr) (left right : List ℕ)
    (hl : Represents left a) (hr : Represents right b) (k : ℕ) :
    entry kind a.size b.size left right k=(mergeBag kind a b).state k := by
  rw [entry_eq_mergeEntry kind a.size b.size left right k
    (fun i hi => (hl i).trans (BagExpr.state_zero_of_size_lt a i hi))
    (fun j hj => (hr j).trans (BagExpr.state_zero_of_size_lt b j hj))]
  exact mergeEntry_correct kind a b left right hl hr k
lemma represented_support (kind : Kind) (a b : BagExpr) (left right : List ℕ)
    (hl : Represents left a) (hr : Represents right b) (k : ℕ) (hk:a.size+b.size < k) :
    entry kind a.size b.size left right k=0 := by
  rw [represented_entry kind a b left right hl hr k]
  exact BagExpr.state_zero_of_size_lt _ k (by simpa only [mergeBag_size] using hk)


def prefixValue (kind : Kind) (a b : ℕ) (left right : List ℕ) (k i j r : ℕ) : ℕ :=
  (∑u∈Finset.range i,∑v∈Finset.range (b+1),∑w∈Finset.range (a+1),contribution kind left right k u v w)+
    (∑v∈Finset.range j,∑w∈Finset.range (a+1),contribution kind left right k i v w)+
    (∑w∈Finset.range r,contribution kind left right k i j w)
lemma prefix_zero (kind : Kind) (a b : ℕ) (left right : List ℕ) (k : ℕ) :
    prefixValue kind a b left right k 0 0 0=0 := by simp [prefixValue]
lemma prefix_step (kind : Kind) (a b : ℕ) (left right : List ℕ) (k i j r : ℕ) :
    prefixValue kind a b left right k i j r+contribution kind left right k i j r=
      prefixValue kind a b left right k i j (r+1) := by
  simp only [prefixValue,Finset.sum_range_succ]
  omega
lemma prefix_row (kind : Kind) (a b : ℕ) (left right : List ℕ) (k i j : ℕ) :
    prefixValue kind a b left right k i j (a+1)=prefixValue kind a b left right k i (j+1) 0 := by
  simp only [prefixValue,Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty,Nat.add_zero]
  omega
lemma prefix_plane (kind : Kind) (a b : ℕ) (left right : List ℕ) (k i : ℕ) :
    prefixValue kind a b left right k i (b+1) 0=prefixValue kind a b left right k (i+1) 0 0 := by
  simp only [prefixValue,Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty,Nat.add_zero]
lemma prefix_complete (kind : Kind) (a b : ℕ) (left right : List ℕ) (k : ℕ) :
    prefixValue kind a b left right k (a+1) 0 0=entry kind a b left right k := by
  simp [prefixValue,entry]
lemma prefix_le_entry (kind : Kind) (a b : ℕ) (left right : List ℕ) (k i j r : ℕ)
    (hi:i ≤ a) (hj:j ≤ b) (hr:r ≤ a+1) :
    prefixValue kind a b left right k i j r ≤ entry kind a b left right k := by
  let f := contribution kind left right k
  have hR : (∑w∈Finset.range r,f i j w) ≤ ∑w∈Finset.range (a+1),f i j w :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hr) (fun _ _ _ => Nat.zero_le _)
  have hJ : (∑v∈Finset.range (j+1),∑w∈Finset.range (a+1),f i v w) ≤ 
      ∑v∈Finset.range (b+1),∑w∈Finset.range (a+1),f i v w :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun _ _ _ => Nat.zero_le _)
  have hI : (∑u∈Finset.range (i+1),∑v∈Finset.range (b+1),∑w∈Finset.range (a+1),f u v w) ≤ 
      ∑u∈Finset.range (a+1),∑v∈Finset.range (b+1),∑w∈Finset.range (a+1),f u v w :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_range_succ] at hI hJ
  dsimp only [f] at hR hJ hI
  unfold prefixValue entry
  change _ ≤ ∑u∈Finset.range (a+1),∑v∈Finset.range (b+1),∑w∈Finset.range (a+1),f u v w
  dsimp only [f] at *
  omega

lemma entry_bound (n : ℕ) (kind : Kind) (a b : ℕ) (left right : List ℕ) (k : ℕ)
    (ha:a ≤ n) (hb:b ≤ n) :
    entry kind a b left right k ≤ 2^(CoefficientRow.entryExponent (CoefficientRow.inputSize n left right)) := by
  let S := CoefficientRow.inputSize n left right
  have hn : n ≤ S := by unfold S CoefficientRow.inputSize;omega
  have hL (i : ℕ) : read left i ≤ 2^S := CoefficientRow.read_bound left i S (by unfold S CoefficientRow.inputSize;omega)
  have hR (j : ℕ) : read right j ≤ 2^S := CoefficientRow.read_bound right j S (by unfold S CoefficientRow.inputSize;omega)
  change entry kind a b left right k ≤ 2^(CoefficientRow.entryExponent S)
  unfold entry
  rw [show CoefficientRow.entryExponent S=((CoefficientRow.termExponent S+(S+1))+(S+1))+(S+1) by unfold CoefficientRow.entryExponent;omega]
  apply CoefficientRow.sum_range_bound S _ (a+1) (by omega)
  intro i hi
  apply CoefficientRow.sum_range_bound S _ (b+1) (by omega)
  intro j hj
  apply CoefficientRow.sum_range_bound S _ (a+1) (by omega)
  intro r hr
  unfold contribution
  split_ifs
  · exact CoefficientRow.cross_term_bound S _ _ i j r (hL i) (hR j)
      (by have := Finset.mem_range.mp hi;omega) (by have := Finset.mem_range.mp hj;omega)
  · exact Nat.zero_le _
lemma prefix_bound (n : ℕ) (kind : Kind) (a b : ℕ) (left right : List ℕ) (k i j r : ℕ)
    (ha:a ≤ n) (hb:b ≤ n) (hi:i ≤ a) (hj:j ≤ b) (hr:r ≤ a+1) :
    prefixValue kind a b left right k i j r ≤ 2^(CoefficientRow.entryExponent (CoefficientRow.inputSize n left right)) :=
  (prefix_le_entry kind a b left right k i j r hi hj hr).trans (entry_bound n kind a b left right k ha hb)
end HiddenCircuits.DH.Runtime.UniformCoefficientModel
