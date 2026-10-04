import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Tactic

/-! Actual finite path expansion of arbitrary interleaved matrix words. -/
namespace HiddenCircuits.Circuit
universe u
open scoped BigOperators
variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Semiring R]

/-- Successive states after each edge, including the final state. -/
def StatePath (ι : Type u) : ℕ → Type u
  | 0 => PUnit
  | n+1 => ι × StatePath ι n

instance statePathFintype (ι : Type*) [Fintype ι] : (n : ℕ) → Fintype (StatePath ι n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n+1 => by
    letI := statePathFintype ι n
    exact inferInstanceAs (Fintype (ι × StatePath ι n))

def pathEnd : (n : ℕ) → ι → StatePath ι n → ι
  | 0,s,_ => s
  | n+1,_,p => pathEnd n p.1 p.2

def pathWeight : (w : List (Matrix ι ι R)) → ι → StatePath ι w.length → R
  | [],_,_ => 1
  | A::w,s,p => A s p.1 * pathWeight w p.1 p.2

/-- Every actual product entry is the sum over its finite state paths. -/
theorem product_entry_sum_paths (w : List (Matrix ι ι R)) (s t : ι) :
    w.prod s t = ∑ p : StatePath ι w.length,
      if pathEnd w.length s p = t then pathWeight w s p else 0 := by
  induction w generalizing s with
  | nil =>
    simp only [List.prod_nil,List.length_nil]
    change (1 : Matrix ι ι R) s t = ∑ p : PUnit, if s=t then 1 else 0
    simp [Matrix.one_apply]
  | cons A w ih =>
    rw [List.prod_cons,Matrix.mul_apply]
    change (∑ j, A s j * w.prod j t) =
      ∑ p : ι × StatePath ι w.length,
        if pathEnd w.length p.1 p.2=t then A s p.1*pathWeight w p.1 p.2 else 0
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j hj
    rw [ih j,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    split_ifs <;> simp

/-- Finite path sums can be grouped exactly by any finite statistic, such as marked gate counts. -/
theorem sum_group_by {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (weight : α → R) :
    (∑ a, weight a) = ∑ b, ∑ a, if f a=b then weight a else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  simp

/-- Regrouping preserves the common class-dependent factor for arbitrary interleaving. -/
theorem sum_group_factor {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (weight : α → R) (factor : β → R) :
    (∑ a, weight a * factor (f a)) =
      ∑ b, (∑ a, if f a=b then weight a else 0) * factor b := by
  rw [sum_group_by f (fun a => weight a * factor (f a))]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases h : f a=b <;> simp [h]

end HiddenCircuits.Circuit
