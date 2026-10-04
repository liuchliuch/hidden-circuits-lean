import HiddenCircuits.Approximation.SelfReduction.Runtime.CoinSlices
import HiddenCircuits.Approximation.SamplerRuntime.CoinLists

/-! Total extraction of a finite coin tape from a physical bit list. The
all-input driver rejects insufficient lists; on sufficient lists no padding is
used and the unread suffix is identified exactly. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open Complexity

 def tapeOfList (n : ℕ) (xs : BitString) : CoinTape n := fun i => xs[i.val]?.getD false

 theorem ofFn_tapeOfList (n : ℕ) (xs : BitString) (hn : n ≤ xs.length) :
    List.ofFn (tapeOfList n xs)=xs.take n := by
  apply List.ext_getElem
  · simp [List.length_take,Nat.min_eq_left hn]
  · intro i hi hj
    have hin : i < n := by simpa using hi
    have hix : i < xs.length := lt_of_lt_of_le hin hn
    simp [tapeOfList,List.getElem?_eq_getElem hix]

 theorem tapeOfList_append_drop (n : ℕ) (xs : BitString) (hn : n ≤ xs.length) :
    List.ofFn (tapeOfList n xs)++xs.drop n=xs := by
  rw [ofFn_tapeOfList n xs hn]
  exact List.take_append_drop n xs

 theorem tapeOfList_ofFn (n : ℕ) (r : CoinTape n) : tapeOfList n (List.ofFn r)=r := by
  funext i
  simp [tapeOfList]

 theorem tapeOfList_ofFn_restrict {n m : ℕ} (h : n ≤ m) (r : CoinTape m) :
    tapeOfList n (List.ofFn r)=SamplerRuntime.CoinLists.restrictTape h r := by
  funext i
  have hi : i.val < m := lt_of_lt_of_le i.isLt h
  simp [tapeOfList,SamplerRuntime.CoinLists.restrictTape,hi]

end HiddenCircuits.Approximation.SelfReduction.Runtime
