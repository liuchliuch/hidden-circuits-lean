import HiddenCircuits.Approximation.SamplerRuntime.Step
import HiddenCircuits.Approximation.SamplerRuntime.CoinLists
import HiddenCircuits.Approximation.FiniteChains.SwitchKernel

/-! Exact bit-order correspondence with the analyzed finite fair-coin kernel. -/
namespace HiddenCircuits.Approximation.SamplerRuntime
open Complexity FiniteChains
open scoped BigOperators

namespace UnaryDecode
lemma little_sum (m : ℕ) (r : CoinTape m) :
    little (List.ofFn r)=∑i : Fin m,bit (r i)*2^i.val := by
  induction m with
  | zero => simp [little,value]
  | succ m ih =>
    rw [List.ofFn_succ,little_cons,ih,Fin.sum_univ_succ]
    simp only [Fin.val_zero,pow_zero,Nat.mul_one,Fin.val_succ,pow_succ]
    simp_rw [←Nat.mul_assoc]
    rw [←Finset.sum_mul]
    ring

lemma little_ofFn (m : ℕ) (r : CoinTape m) : little (List.ofFn r)=(tapeNumber m r).val := by
  rw [little_sum]
  unfold tapeNumber
  rw [Equiv.trans_apply,finFunctionFinEquiv_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change bit (r i)=(finTwoEquiv.symm (r i)).val
  cases r i <;> rfl
end UnaryDecode

namespace Step
variable {n : ℕ}

lemma first_ofFn (n : ℕ) (r : CoinTape (width n)) :
    first n (List.ofFn r)=(switchProposal (Nat.size n) r).2.1.val := by
  let m := Nat.size n
  have hl : m≤(List.ofFn r).tail.length := by simp [width,m]
  unfold first Proposal.index
  rw [TapeRead.prefix_eq_take _ _ hl]
  rw [←List.drop_one]
  change UnaryDecode.little (((List.ofFn r).drop 1).take m)=_
  rw [CoinLists.splitTape_drop 1 (m+m) r,CoinLists.splitTape_take m m]
  rw [UnaryDecode.little_ofFn]
  rfl

lemma second_ofFn (n : ℕ) (r : CoinTape (width n)) :
    second n (List.ofFn r)=(switchProposal (Nat.size n) r).2.2.val := by
  let m := Nat.size n
  have hl : m≤((List.ofFn r).tail.drop m).length := by simp [width,m];omega
  unfold second Proposal.index
  rw [TapeRead.prefix_eq_take _ _ hl]
  rw [←List.drop_one]
  change UnaryDecode.little ((((List.ofFn r).drop 1).drop m).take m)=_
  rw [CoinLists.splitTape_drop 1 (m+m) r,CoinLists.splitTape_drop m m]
  rw [List.take_of_length_le (by simp),UnaryDecode.little_ofFn]
  rfl

lemma hold_ofFn (n : ℕ) (r : CoinTape (width n)) :
    (List.ofFn r).headD false=(switchProposal (Nat.size n) r).1 := by
  change (List.ofFn (n:=1+(Nat.size n+Nat.size n)) r).headD false=_
  rw [List.ofFn_add,List.ofFn_succ]
  rfl

/-- The literal decoder uses precisely the coordinate order of tapeNumber. -/
theorem step_ofFn (E : MonotoneEndpoints n) (π : E.Permutations) (r : CoinTape (width n)) :
    step E π (List.ofFn r)=MonotoneSwitch.step E (Nat.size n) π r := by
  unfold step
  rw [first_ofFn,second_ofFn,hold_ofFn]
  unfold move MonotoneSwitch.step
  by_cases hh : (switchProposal (Nat.size n) r).1=true
  · simp [hh]
  · have hf : (switchProposal (Nat.size n) r).1=false := Bool.eq_false_iff.mpr hh
    by_cases hi : (switchProposal (Nat.size n) r).2.1.val<n
    · by_cases hj : (switchProposal (Nat.size n) r).2.2.val<n
      · simp [hf,hi,hj]
      · simp [hf,hi,hj]
    · simp [hf,hi]

lemma index_append (m : ℕ) (xs ys : BitString) (h : m≤xs.length) :
    Proposal.index m (xs++ys)=Proposal.index m xs := by
  simp only [Proposal.index]
  rw [TapeRead.prefix_eq_take _ _ (by simp;omega),TapeRead.prefix_eq_take _ _ h,List.take_append_of_le_length h]

lemma step_append (E : MonotoneEndpoints n) (π : E.Permutations) (xs ys : BitString) (h : width n≤xs.length) :
    step E π (xs++ys)=step E π xs := by
  have hpos : xs≠[] := by intro hz;subst xs;simp [width] at h
  have hm : Nat.size n≤xs.tail.length := by simp only [List.length_tail];unfold width at h;omega
  have hm2 : Nat.size n≤(xs.tail.drop (Nat.size n)).length := by
    simp only [List.length_drop,List.length_tail];unfold width at h;omega
  simp only [step,first,second,List.tail_append_of_ne_nil hpos]
  rw [index_append _ _ _ hm,List.drop_append_of_le_length hm,index_append _ _ _ hm2]
  congr 1
  cases xs with
  | nil => exact (hpos rfl).elim
  | cons b xs => rfl

end Step
end HiddenCircuits.Approximation.SamplerRuntime
