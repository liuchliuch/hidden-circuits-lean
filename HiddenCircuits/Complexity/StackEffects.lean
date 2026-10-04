import HiddenCircuits.Complexity.TM2Locality

/-! A TM2 macrostep acts on each stack by replacing a bounded prefix and shifting
its untouched suffix. The instrumentation records these effects exactly. -/
namespace HiddenCircuits.Complexity

@[ext] structure StackEffect (α : Type*) where
  removed : ℕ
  inserted : List α

namespace StackEffect
variable {α : Type*}
def identity : StackEffect α := ⟨0,[]⟩
def apply (e : StackEffect α) (l : List α) : List α := e.inserted ++ l.drop e.removed
def push (a : α) (e : StackEffect α) : StackEffect α := ⟨e.removed,a::e.inserted⟩
def pop (e : StackEffect α) : StackEffect α :=
  match e.inserted with
  | [] => ⟨e.removed+1,[]⟩
  | _::xs => ⟨e.removed,xs⟩

@[simp] theorem identity_apply (l : List α) : identity.apply l = l := by simp [identity,apply]
@[simp] theorem push_apply (a : α) (e : StackEffect α) (l : List α) :
    (push a e).apply l = a::e.apply l := rfl
@[simp] theorem pop_apply (e : StackEffect α) (l : List α) :
    e.pop.apply l = (e.apply l).tail := by
  rcases e with ⟨r,xs⟩
  cases xs <;> simp [pop,apply,List.tail_drop]

theorem getElem?_apply (e : StackEffect α) (l : List α) (j : ℕ) :
    (e.apply l)[j]? = if j < e.inserted.length then e.inserted[j]?
      else l[j-e.inserted.length+e.removed]? := by
  simp only [apply,List.getElem?_append,List.getElem?_drop,Nat.add_comm]

def cost (e : StackEffect α) : ℕ := e.removed+e.inserted.length
@[simp] theorem identity_cost : (identity (α := α)).cost = 0 := rfl
@[simp] theorem push_cost (a : α) (e : StackEffect α) : (push a e).cost = e.cost+1 := by
  simp [cost,push];omega
lemma pop_cost (e : StackEffect α) : e.pop.cost ≤ e.cost+1 := by
  rcases e with ⟨r,xs⟩
  cases xs <;> simp [pop,cost] <;> omega
end StackEffect

namespace TM2Effects
open Turing.TM2
variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*} [DecidableEq K]

abbrev Effects := (k : K) → StackEffect (Γ k)

def instrument : Stmt Γ Λ σ → Stmt Γ Λ (σ × Effects (Γ := Γ))
  | .push k f s => .push k (fun z => f z.1)
      (.load (fun z => (z.1,Function.update z.2 k (StackEffect.push (f z.1) (z.2 k)))) (instrument s))
  | .peek k f s => .peek k (fun z a => (f z.1 a,z.2)) (instrument s)
  | .pop k f s => .pop k (fun z a => (f z.1 a,Function.update z.2 k (z.2 k).pop)) (instrument s)
  | .load f s => .load (fun z => (f z.1,z.2)) (instrument s)
  | .branch f s t => .branch (fun z => f z.1) (instrument s) (instrument t)
  | .goto f => .goto (fun z => f z.1)
  | .halt => .halt

def erase (c : Cfg Γ Λ (σ × Effects (Γ := Γ))) : Cfg Γ Λ σ := ⟨c.l,c.var.1,c.stk⟩

/-- Instrumentation changes none of the original operational behavior. -/
theorem instrument_erase (s : Stmt Γ Λ σ) (v : σ) (E : Effects (Γ := Γ))
    (S : ∀ k, List (Γ k)) :
    erase (stepAux (instrument s) (v,E) S) = stepAux s v S := by
  induction s generalizing v E S with
  | push k f s ih => exact ih _ _ _
  | peek k f s ih => exact ih _ _ _
  | pop k f s ih => exact ih _ _ _
  | load f s ih => exact ih _ _ _
  | branch f s t ihs iht => cases hf : f v <;> simp [instrument,stepAux,hf,ihs,iht]
  | goto f => rfl
  | halt => rfl

def Applies (E : Effects (Γ := Γ)) (base S : ∀ k, List (Γ k)) : Prop :=
  ∀ k, (E k).apply (base k) = S k

/-- The effect state is a proved exact description of all stack mutations. -/
theorem instrument_applies (s : Stmt Γ Λ σ) (v : σ) (E : Effects (Γ := Γ))
    (base S : ∀ k, List (Γ k)) (h : Applies E base S) :
    Applies (stepAux (instrument s) (v,E) S).var.2 base
      (stepAux (instrument s) (v,E) S).stk := by
  induction s generalizing v E S with
  | push k f s ih =>
    apply ih
    intro j
    by_cases hj : j = k
    · subst j; simpa using congrArg (List.cons (f v)) (h k)
    · simpa [Function.update_of_ne hj] using h j
  | peek k f s ih => exact ih _ _ _ h
  | pop k f s ih =>
    apply ih
    intro j
    by_cases hj : j = k
    · subst j; simpa using congrArg List.tail (h k)
    · simpa [Function.update_of_ne hj] using h j
  | load f s ih => exact ih _ _ _ h
  | branch f s t ihs iht => cases hf : f v <;> simp [instrument,stepAux,hf,ihs,iht,h]
  | goto f => exact h
  | halt => exact h

theorem instrument_cost (s : Stmt Γ Λ σ) (v : σ) (E : Effects (Γ := Γ))
    (S : ∀ k, List (Γ k)) (B : ℕ) (hE : ∀ k, (E k).cost ≤ B) :
    ∀ k, ((stepAux (instrument s) (v,E) S).var.2 k).cost ≤
      B+TM2Locality.inspectionBudget s := by
  induction s generalizing v E S B with
  | push k f s ih =>
    have hn : ∀ j, (Function.update E k (StackEffect.push (f v) (E k)) j).cost ≤ B+1 := by
      intro j
      by_cases hj : j = k
      · subst j; simpa using Nat.add_le_add_right (hE k) 1
      · simpa [Function.update_of_ne hj] using (hE j).trans (Nat.le_add_right B 1)
    simpa [instrument,stepAux,TM2Locality.inspectionBudget,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      using ih v _ _ (B+1) hn
  | peek k f s ih =>
    intro j
    exact (ih _ E S B hE j).trans (by simp [TM2Locality.inspectionBudget])
  | pop k f s ih =>
    have hn : ∀ j, (Function.update E k (E k).pop j).cost ≤ B+1 := by
      intro j
      by_cases hj : j = k
      · subst j; simp only [Function.update_self]
        exact (StackEffect.pop_cost _).trans (Nat.add_le_add_right (hE k) 1)
      · simpa [Function.update_of_ne hj] using (hE j).trans (Nat.le_add_right B 1)
    simpa [instrument,stepAux,TM2Locality.inspectionBudget,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      using ih _ _ _ (B+1) hn
  | load f s ih =>
    intro j
    exact (ih _ E S B hE j).trans (by simp [TM2Locality.inspectionBudget])
  | branch f s t ihs iht =>
    intro j
    cases hf : f v with
    | false =>
      simpa [instrument,stepAux,hf] using (iht v E S B hE j).trans
        (show B+TM2Locality.inspectionBudget t ≤ B+TM2Locality.inspectionBudget (.branch f s t) by
          simp [TM2Locality.inspectionBudget];omega)
    | true =>
      simpa [instrument,stepAux,hf] using (ihs v E S B hE j).trans
        (show B+TM2Locality.inspectionBudget s ≤ B+TM2Locality.inspectionBudget (.branch f s t) by
          simp [TM2Locality.inspectionBudget];omega)
  | goto f => simpa [instrument,stepAux,TM2Locality.inspectionBudget] using hE
  | halt => simpa [instrument,stepAux,TM2Locality.inspectionBudget] using hE

def effectsOf (s : Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) : Effects (Γ := Γ) :=
  (stepAux (instrument s) (v,fun _ => StackEffect.identity) S).var.2

theorem effectsOf_cost (s : Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (k : K) :
    (effectsOf s v S k).cost ≤ TM2Locality.inspectionBudget s := by
  simpa [effectsOf] using instrument_cost s v (fun _ => StackEffect.identity) S 0 (by simp) k

/-- Every actual output stack consists of an inserted prefix and an untouched,
shifted input suffix. -/
theorem effectsOf_apply (s : Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (k : K) :
    (effectsOf s v S k).apply (S k) = (stepAux s v S).stk k := by
  have he := instrument_applies s v (fun _ => StackEffect.identity) S S
    (fun _ => StackEffect.identity_apply _)
  have hs := congrArg (fun c : Cfg Γ Λ σ => c.stk k)
    (instrument_erase s v (fun _ => StackEffect.identity) S)
  exact (he k).trans hs

lemma instrument_budget (s : Stmt Γ Λ σ) :
    TM2Locality.inspectionBudget (instrument s) ≤ 2*TM2Locality.inspectionBudget s := by
  induction s <;> simp only [instrument,TM2Locality.inspectionBudget] <;> omega

/-- The complete effect (including inserted symbols and suffix shift) depends
only on a machine-constant prefix, independently of input stack lengths. -/
theorem effectsOf_local (s : Stmt Γ Λ σ) (v : σ) (S T : ∀ k, List (Γ k))
    (h : TM2Locality.Agree (2*TM2Locality.inspectionBudget s) S T) :
    effectsOf s v S = effectsOf s v T := by
  have he := TM2Locality.control_local (instrument s) (v,fun _ => StackEffect.identity) S T
    (TM2Locality.agree_mono h (instrument_budget s))
  exact congrArg Prod.snd he.2

/-- Every output cell depends only on a fixed-size control prefix and a bounded
set of shifted input cells. The number of dependencies is independent of stack
length and the requested cell index. -/
theorem stepAux_cell_local (s : Stmt Γ Λ σ) (v : σ) (S T : ∀ k, List (Γ k)) (j : ℕ)
    (hprefix : TM2Locality.Agree (2*TM2Locality.inspectionBudget s) S T)
    (hwindow : ∀ k a b, a ≤ TM2Locality.inspectionBudget s →
      b ≤ TM2Locality.inspectionBudget s → (S k)[j-a+b]? = (T k)[j-a+b]?) (k : K) :
    ((stepAux s v S).stk k)[j]? = ((stepAux s v T).stk k)[j]? := by
  rw [← effectsOf_apply s v S k,← effectsOf_apply s v T k]
  have he := congrFun (effectsOf_local s v S T hprefix) k
  rw [← he]
  simp only [StackEffect.getElem?_apply]
  split_ifs with hj
  · rfl
  · have hc := effectsOf_cost s v S k
    unfold StackEffect.cost at hc
    exact hwindow k _ _ (by omega) (by omega)

end TM2Effects
end HiddenCircuits.Complexity
