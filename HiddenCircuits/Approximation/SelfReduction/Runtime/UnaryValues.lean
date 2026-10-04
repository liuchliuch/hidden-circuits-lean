import HiddenCircuits.Approximation.SelfReduction.Runtime.UnaryEmit

namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity

def unaryValues (xs : List ℕ) : BitString := encodeBitList (xs.map (fun x => List.replicate x true))

 theorem unaryValues_cons (x : ℕ) (xs : List ℕ) :
    unaryValues (x::xs) = (true::pairBits (List.replicate x true) []) ++ unaryValues xs := by
  simp [unaryValues, encodeBitList, pairBits_unary]

 theorem unaryValues_reverse_cons (x : ℕ) (xs : List ℕ) :
    (unaryValues (x::xs)).reverse = (unaryValues xs).reverse ++ (true::pairBits (List.replicate x true) []).reverse := by
  rw [unaryValues_cons, List.reverse_append]

 theorem unaryValues_length (xs : List ℕ) : (unaryValues xs).length=2*xs.sum+2*xs.length := by
  simp [unaryValues, encodeBitList_length, List.map_map, Function.comp_def, Nat.mul_comm]

 theorem unaryValues_length_bound (xs : List ℕ) (B : ℕ) (hxs : ∀ x ∈ xs, x ≤ B) :
    (unaryValues xs).length ≤ 2*xs.length*(B+1) := by
  have hs : xs.sum ≤ xs.length*B := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have hx := hxs x (by simp)
      have ht := ih (fun y hy => hxs y (by simp [hy]))
      simp only [List.sum_cons, List.length_cons]
      nlinarith
  rw [unaryValues_length]
  nlinarith

end HiddenCircuits.Approximation.SelfReduction.Runtime
