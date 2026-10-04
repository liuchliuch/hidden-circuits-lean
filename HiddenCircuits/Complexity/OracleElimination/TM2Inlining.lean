import HiddenCircuits.Complexity.TM2BitSimulation

/-! Operational inlining of an arbitrary finite TM2 on a disjoint private bank
of typed stacks. A source halt becomes an actual continuation jump. Register
and stack contents are preserved exactly; no simulator hypothesis is assumed. -/
namespace HiddenCircuits.Complexity.OracleElimination
open Turing.TM2

section Evaluation
variable {α β : Type} {f : α → Option α} {g : β → Option β}

def Eval (f : α → Option α) (a b : α) (n : ℕ) : Prop :=
  Nonempty (StateTransition.EvalsToInTime f a (some b) n)

namespace Eval

theorem refl (f : α → Option α) (a : α) : Eval f a a 0 :=
  ⟨StateTransition.EvalsToInTime.refl f a⟩

theorem single {a b : α} (h : f a = some b) : Eval f a b 1 :=
  ⟨⟨⟨1,h⟩,le_rfl⟩⟩

theorem trans {a b c : α} {m n : ℕ} (h : Eval f a b m) (h' : Eval f b c n) :
    Eval f a c (m+n) := by
  obtain ⟨h⟩ := h
  obtain ⟨h'⟩ := h'
  exact ⟨by simpa [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans f m n a b (some c) h h'⟩

theorem mono {a b : α} {m n : ℕ} (h : Eval f a b m) (hm : m ≤ n) : Eval f a b n := by
  obtain ⟨h⟩ := h
  exact ⟨⟨h.toEvalsTo,h.steps_le_m.trans hm⟩⟩

private theorem iterate_none (f : α → Option α) (n : ℕ) :
    (fun o : Option α => o.bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih];rfl

private theorem simulate_iterate (φ : α → β)
    (h : ∀ a b, f a = some b → g (φ a) = some (φ b)) (n : ℕ) {a b : α}
    (he : (fun o : Option α => o.bind f)^[n] (some a) = some b) :
    (fun o : Option β => o.bind g)^[n] (some (φ a)) = some (φ b) := by
  induction n generalizing a with
  | zero => cases Option.some.inj he;rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply] at he ⊢
    cases hs : f a with
    | none =>
      simp only [Option.bind_some,hs] at he
      rw [iterate_none] at he
      contradiction
    | some c =>
      simp only [Option.bind_some,hs] at he
      simp only [Option.bind_some,h a c hs]
      exact ih he

/-- Transport a terminating computation through a proved one-step simulation.
No condition is imposed on the destination after the simulated halt. -/
theorem map (φ : α → β)
    (h : ∀ a b, f a = some b → g (φ a) = some (φ b))
    {a b : α} {n : ℕ} (he : Eval f a b n) : Eval g (φ a) (φ b) n := by
  obtain ⟨he⟩ := he
  exact ⟨⟨⟨he.steps,simulate_iterate φ h he.steps he.evals_in_steps⟩,he.steps_le_m⟩⟩
end Eval
end Evaluation

section Inlining
variable {A K : Type} {ΓA : A → Type} {Γ : K → Type} {Λ L σ V : Type}
variable [DecidableEq A] [DecidableEq K]

/-- Disjoint public and private banks retain their original symbol types. -/
def Alphabet (ΓA : A → Type) (Γ : K → Type) : A ⊕ K → Type
  | .inl a => ΓA a
  | .inr k => Γ k

def store (S : ∀ a,List (ΓA a)) (T : ∀ k,List (Γ k)) :
    ∀ z, List (Alphabet ΓA Γ z)
  | .inl a => S a
  | .inr k => T k

@[simp] theorem store_inl (S : ∀ a,List (ΓA a)) (T : ∀ k,List (Γ k)) (a : A) :
    store S T (.inl a) = S a := rfl
@[simp] theorem store_inr (S : ∀ a,List (ΓA a)) (T : ∀ k,List (Γ k)) (k : K) :
    store S T (.inr k) = T k := rfl

@[simp] theorem store_update_right (S : ∀ a,List (ΓA a)) (T : ∀ k,List (Γ k))
    (k : K) (xs : List (Γ k)) :
    Function.update (store S T) (.inr k) xs = store S (Function.update T k xs) := by
  funext z
  cases z with
  | inl a => simp [Function.update_apply,store]
  | inr j =>
    by_cases hj : j = k
    · subst j;simp
    · simp [Function.update_of_ne hj,Function.update_of_ne (show Sum.inr j ≠ Sum.inr k from fun h => hj (Sum.inr.inj h))]

/-- Translate only primitive typed-stack operations and finite register maps. -/
def inline (label : Option Λ → L) : Stmt Γ Λ σ → Stmt (Alphabet ΓA Γ) L (σ × V)
  | .push k f s => .push (.inr k) (fun v => f v.1) (inline label s)
  | .peek k f s => .peek (.inr k) (fun v b => (f v.1 b,v.2)) (inline label s)
  | .pop k f s => .pop (.inr k) (fun v b => (f v.1 b,v.2)) (inline label s)
  | .load f s => .load (fun v => (f v.1,v.2)) (inline label s)
  | .branch f s t => .branch (fun v => f v.1) (inline label s) (inline label t)
  | .goto f => .goto (fun v => label (some (f v.1)))
  | .halt => .goto (fun _ => label none)

def config (label : Option Λ → L) (S : ∀ a,List (ΓA a)) (v : V)
    (c : Cfg Γ Λ σ) : Cfg (Alphabet ΓA Γ) L (σ × V) :=
  ⟨some (label c.l),(c.var,v),store S c.stk⟩

/-- Exact statement-level correctness, including the continuation jump. -/
theorem inline_stepAux (label : Option Λ → L) (S : ∀ a,List (ΓA a)) (v : V)
    (s : Stmt Γ Λ σ) (w : σ) (T : ∀ k,List (Γ k)) :
    stepAux (inline (ΓA := ΓA) label s) (w,v) (store S T) =
      config label S v (stepAux s w T) := by
  induction s generalizing w T with
  | push k f s ih => simpa [inline,stepAux] using ih w (Function.update T k (f w :: T k))
  | peek k f s ih => exact ih _ T
  | pop k f s ih => simpa [inline,stepAux] using ih (f w (T k).head?) (Function.update T k (T k).tail)
  | load f s ih => exact ih _ T
  | branch f s t ihs iht => cases h : f w <;> simp [inline,stepAux,h,ihs,iht]
  | goto f => rfl
  | halt => rfl

/-- A complete private-bank run inlines with the same macrostep bound. -/
theorem inline_eval (code : Λ → Stmt Γ Λ σ) (code' : L → Stmt (Alphabet ΓA Γ) L (σ × V))
    (label : Option Λ → L) (hc : ∀ l,code' (label (some l)) = inline label (code l))
    (S : ∀ a,List (ΓA a)) (v : V) {a b : Cfg Γ Λ σ} {n : ℕ}
    (h : Eval (step code) a b n) :
    Eval (step code') (config label S v a) (config label S v b) n := by
  apply h.map (config label S v)
  intro c d hd
  cases c with
  | mk l w T =>
    cases l with
    | none => contradiction
    | some l =>
      have he : d = stepAux (code l) w T := (Option.some.inj hd).symm
      subst d
      simp only [config,step,hc]
      exact congrArg some (inline_stepAux label S v (code l) w T)

end Inlining
end HiddenCircuits.Complexity.OracleElimination
