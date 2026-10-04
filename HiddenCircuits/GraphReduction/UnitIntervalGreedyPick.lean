import HiddenCircuits.GraphReduction.UnitIntervalGreedy
import Mathlib.Data.List.MinMax

/-! A concrete count-based candidate selector. Its key is bounded by a quadratic
polynomial in the number of vertices, and it does not inspect any representation. -/
namespace HiddenCircuits.GraphReduction.UnitIntervalGreedy
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma degree_le (v : V) : degree G v ≤ Fintype.card V := by
  exact (Finset.card_filter_le _ _).trans_eq Finset.card_univ

/-- Maximizing this nonnegative key implements maximum prefix score with
minimum closed-degree tie breaking. -/
def priority (S : Finset V) (v : V) : ℕ :=
  (Fintype.card V+1)*score G S v + (Fintype.card V-degree G v)

def choose (S R : Finset V) : Option V := (R.sort (· ≤ ·)).argmax (priority G S)

lemma priority_le_iff (S : Finset V) (x y : V) :
    priority G S x ≤ priority G S y ↔
      score G S x ≤ score G S y ∧
        (score G S x = score G S y → degree G y ≤ degree G x) := by
  have hx := degree_le G x
  have hy := degree_le G y
  have hdx := Nat.sub_add_cancel hx
  have hdy := Nat.sub_add_cancel hy
  unfold priority
  constructor
  · intro h
    have hscore : score G S x ≤ score G S y := by
      by_contra hn
      have hh : score G S y+1 ≤ score G S x := by omega
      have hm := Nat.mul_le_mul_left (Fintype.card V+1) hh
      nlinarith
    exact ⟨hscore,by intro he; rw [he] at h; omega⟩
  · rintro ⟨hscore,htie⟩
    rcases eq_or_lt_of_le hscore with he | hlt
    · have := htie he; rw [he]; omega
    · have hm := Nat.mul_le_mul_left (Fintype.card V+1) (Nat.succ_le_of_lt hlt)
      nlinarith

lemma choose_spec (S R : Finset V) {y : V} (hy : choose G S R = some y) :
    Preferred G S R y := by
  have hym : y ∈ (R.sort (· ≤ ·)).argmax (priority G S) := hy
  refine ⟨(Finset.mem_sort (· ≤ ·)).mp (List.argmax_mem hym),?_⟩
  intro x hx
  exact (priority_le_iff G S x y).mp (List.le_of_mem_argmax ((Finset.mem_sort (· ≤ ·)).mpr hx) hym)

@[simp] lemma choose_none (S R : Finset V) : choose G S R = none ↔ R = ∅ := by
  rw [choose,List.argmax_eq_none]
  constructor
  · intro h
    apply Finset.card_eq_zero.mp
    have := congrArg List.length h
    simpa using this
  · intro h; subst R; simp

lemma priority_bound (S : Finset V) (v : V) :
    priority G S v ≤ (Fintype.card V+1)^2 := by
  have hs : score G S v ≤ Fintype.card V :=
    (Finset.card_filter_le _ _).trans (Finset.card_le_univ _)
  have hd : Fintype.card V-degree G v ≤ Fintype.card V := Nat.sub_le _ _
  unfold priority
  nlinarith

end HiddenCircuits.GraphReduction.UnitIntervalGreedy
