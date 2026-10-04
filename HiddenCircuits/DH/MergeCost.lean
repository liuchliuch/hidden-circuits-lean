import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-! Exact pair charging for a binary bag-merge forest.
These are arithmetic support lemmas. A graph execution must still be connected to this tree.
No preprocessing algorithm or actual machine-cost bound is assumed or asserted here. -/
namespace HiddenCircuits.DH

inductive MergeTree where
  | leaf
  | merge (left right : MergeTree)
  deriving DecidableEq

def MergeTree.size : MergeTree → ℕ
  | .leaf => 1
  | .merge l r => l.size + r.size

def MergeTree.charge : MergeTree → ℕ
  | .leaf => 0
  | .merge l r => l.charge + r.charge + l.size * r.size

lemma MergeTree.size_pos (t : MergeTree) : 0 < t.size := by
  induction t with
  | leaf => simp [size]
  | merge l r hl hr => simp only [size]; omega

lemma MergeTree.square_identity (t : MergeTree) :
    t.size * t.size = t.size + 2 * t.charge := by
  induction t with
  | leaf => simp [size, charge]
  | merge l r hl hr => simp only [size, charge]; nlinarith

lemma twice_choose_two (n : ℕ) : n + 2 * n.choose 2 = n*n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith

/-- Each vertex pair is charged exactly once in its final binary merge tree. -/
theorem MergeTree.charge_eq_choose (t : MergeTree) : t.charge = t.size.choose 2 := by
  have h := t.square_identity
  have h' := twice_choose_two t.size
  omega

def forestSize (ts : List MergeTree) : ℕ := (ts.map MergeTree.size).sum
def forestCharge (ts : List MergeTree) : ℕ := (ts.map MergeTree.charge).sum

/-- The exact final-bag sum in the paper's pair-charge equality. -/
theorem forest_charge_eq_sum_choose (ts : List MergeTree) :
    forestCharge ts = (ts.map fun t => t.size.choose 2).sum := by
  unfold forestCharge
  congr 1
  apply List.map_congr_left
  intro t ht
  exact t.charge_eq_choose

lemma forest_square_bound (ts : List MergeTree) :
    forestSize ts + 2 * forestCharge ts ≤ forestSize ts * forestSize ts := by
  induction ts with
  | nil => simp [forestSize, forestCharge]
  | cons t ts ih =>
    have ht := t.square_identity
    simp only [forestSize, forestCharge, List.map_cons, List.sum_cons] at *
    nlinarith [Nat.zero_le (t.size * (ts.map MergeTree.size).sum)]

/-- The total cross-bag pair charge never exceeds the number of original unordered pairs. -/
theorem forest_charge_le_choose (ts : List MergeTree) :
    forestCharge ts ≤ (forestSize ts).choose 2 := by
  have h := forest_square_bound ts
  have h' := twice_choose_two (forestSize ts)
  omega

/-- Uniform explicit bound for scanning recurrence arrays after swapping the true-twin operands. -/
theorem recurrence_array_cost (a b : ℕ) (ha : b ≤ a) (hb : 1 ≤ b) :
    (b+1)*(a+b+1) ≤ 6*a*b := by
  have h1 : b+1 ≤ 2*b := by omega
  have h2 : a+b+1 ≤ 3*a := by omega
  have h := Nat.mul_le_mul h1 h2
  nlinarith

end HiddenCircuits.DH
