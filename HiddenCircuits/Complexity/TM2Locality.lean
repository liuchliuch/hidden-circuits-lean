import HiddenCircuits.Complexity.TM2Alphabet

/-! Fixed-window locality of a finite TM2 macrostep. The transition's control
and any requested output prefix depend only on a fixed additional input prefix.
This is a proved property of the statement syntax, not a compiler assumption. -/
namespace HiddenCircuits.Complexity.TM2Locality
open Turing.TM2
variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}

/-- A syntax-derived upper bound on sequential stack inspections/removals. -/
def inspectionBudget : Stmt Γ Λ σ → ℕ
  | .push _ _ s => inspectionBudget s+1
  | .peek _ _ s => inspectionBudget s+1
  | .pop _ _ s => inspectionBudget s+1
  | .load _ s => inspectionBudget s+1
  | .branch _ s t => max (inspectionBudget s) (inspectionBudget t)+1
  | .goto _ => 0
  | .halt => 0

def Agree (r : ℕ) (S T : ∀ k, List (Γ k)) : Prop :=
  ∀ k, (S k).take r = (T k).take r

lemma take_mono_eq {α : Type*} {l₁ l₂ : List α} {r s : ℕ}
    (h : l₁.take s = l₂.take s) (hrs : r ≤ s) : l₁.take r = l₂.take r := by
  have he := congrArg (List.take r) h
  simpa only [List.take_take,Nat.min_eq_left hrs] using he

lemma agree_mono {S T : ∀ k, List (Γ k)} {r s : ℕ} (h : Agree s S T) (hrs : r ≤ s) :
    Agree r S T := fun k => take_mono_eq (h k) hrs

lemma head_eq_of_take {α : Type*} {l₁ l₂ : List α} {r : ℕ}
    (h : l₁.take r = l₂.take r) (hr : 0 < r) : l₁.head? = l₂.head? := by
  have he := take_mono_eq h (show 1 ≤ r by omega)
  cases l₁ <;> cases l₂ <;> simp_all

lemma tail_take {α : Type*} (l : List α) (r : ℕ) :
    l.tail.take r = (l.take (r+1)).tail := by cases l <;> simp

lemma take_cons_eq {α : Type*} {l₁ l₂ : List α} {r : ℕ} (a : α)
    (h : l₁.take r = l₂.take r) : (a::l₁).take r = (a::l₂).take r := by
  cases r with
  | zero => rfl
  | succ r =>
    simp only [List.take_succ_cons]
    exact congrArg (List.cons a) (take_mono_eq h (Nat.le_succ r))

variable [DecidableEq K]

/-- Complete control and output-prefix locality for the actual finite statement. -/
theorem stepAux_local (s : Stmt Γ Λ σ) (v : σ) (S T : ∀ k, List (Γ k)) (r : ℕ)
    (h : Agree (inspectionBudget s+r) S T) :
    (stepAux s v S).l = (stepAux s v T).l ∧
    (stepAux s v S).var = (stepAux s v T).var ∧
    Agree r (stepAux s v S).stk (stepAux s v T).stk := by
  induction s generalizing v S T r with
  | push k f s ih =>
    have hbase : Agree (inspectionBudget s+r) S T := agree_mono h (by simp [inspectionBudget] <;> omega)
    have hn : Agree (inspectionBudget s+r)
        (Function.update S k (f v::S k)) (Function.update T k (f v::T k)) := by
      intro j
      by_cases hj : j = k
      · subst j; simp only [Function.update_self]; exact take_cons_eq _ (hbase k)
      · simpa only [Function.update_of_ne hj] using hbase j
    exact ih v _ _ r hn
  | peek k f s ih =>
    have he : (S k).head? = (T k).head? := head_eq_of_take (h k) (by simp [inspectionBudget] <;> omega)
    have hb : Agree (inspectionBudget s+r) S T := agree_mono h (by simp [inspectionBudget] <;> omega)
    simpa only [stepAux,he] using ih (f v (T k).head?) S T r hb
  | pop k f s ih =>
    have he : (S k).head? = (T k).head? := head_eq_of_take (h k) (by simp [inspectionBudget] <;> omega)
    have hn : Agree (inspectionBudget s+r)
        (Function.update S k (S k).tail) (Function.update T k (T k).tail) := by
      intro j
      by_cases hj : j = k
      · subst j
        simp only [Function.update_self,tail_take]
        apply congrArg List.tail
        exact take_mono_eq (h k) (by simp [inspectionBudget] <;> omega)
      · simp only [Function.update_of_ne hj]
        exact take_mono_eq (h j) (by simp [inspectionBudget] <;> omega)
    simpa only [stepAux,he] using ih (f v (T k).head?) _ _ r hn
  | load f s ih =>
    exact ih (f v) S T r (agree_mono h (by simp [inspectionBudget] <;> omega))
  | branch f s t ihs iht =>
    cases hf : f v with
    | false =>
      have hb : Agree (inspectionBudget t+r) S T := agree_mono h (by simp [inspectionBudget] <;> omega)
      simpa [stepAux,hf] using iht v S T r hb
    | true =>
      have hb : Agree (inspectionBudget s+r) S T := agree_mono h (by simp [inspectionBudget] <;> omega)
      simpa [stepAux,hf] using ihs v S T r hb
  | goto f => exact ⟨rfl,rfl,by simpa [inspectionBudget,stepAux] using h⟩
  | halt => exact ⟨rfl,rfl,by simpa [inspectionBudget,stepAux] using h⟩

/-- In particular, all control effects depend only on a machine-constant prefix. -/
theorem control_local (s : Stmt Γ Λ σ) (v : σ) (S T : ∀ k, List (Γ k))
    (h : Agree (inspectionBudget s) S T) :
    (stepAux s v S).l = (stepAux s v T).l ∧
    (stepAux s v S).var = (stepAux s v T).var := by
  have he := stepAux_local s v S T 0 (by simpa using h)
  exact ⟨he.1,he.2.1⟩

end HiddenCircuits.Complexity.TM2Locality
