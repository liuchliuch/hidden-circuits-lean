import HiddenCircuits.Complexity.OracleMachine

/-! Finite execution prefixes and exact charged-cost composition. These are
operational lemmas about actual finite programs, not assumed complexity rules. -/
namespace HiddenCircuits.Complexity.OracleMachine
variable (M : OracleMachine)

inductive Steps (g : BitString → ℕ) : M.Config → M.Config → ℕ → Prop
  | refl (c) : Steps g c c 0
  | next {c d e a b} (h : M.step g c = some (d,a)) (tail : Steps g d e b) :
      Steps g c e (a+b)

namespace Steps
variable {M} {g : BitString → ℕ}

theorem single {c d : M.Config} {a : ℕ} (h : M.step g c = some (d,a)) : M.Steps g c d a := by
  simpa using Steps.next h (Steps.refl d)

theorem trans {c d e : M.Config} {a b : ℕ}
    (h₁ : M.Steps g c d a) (h₂ : M.Steps g d e b) : M.Steps g c e (a+b) := by
  induction h₁ with
  | refl c => simpa using h₂
  | next h tail ih => simpa [Nat.add_assoc] using Steps.next h (ih h₂)

theorem thenRun {c d e : M.Config} {a b : ℕ}
    (h₁ : M.Steps g c d a) (h₂ : M.Runs g d e b) : M.Runs g c e (a+b) := by
  induction h₁ with
  | refl c => simpa using h₂
  | next h tail ih => simpa [Nat.add_assoc] using Runs.next h (ih h₂)

theorem stack_bound {c d : M.Config} {t n : ℕ} (h : M.Steps g c d t)
    (hc : ∀ k, (c.stack k).length ≤ n) : ∀ k, (d.stack k).length ≤ n+t := by
  induction h generalizing n with
  | refl c => simpa using hc
  | next h tail ih => simpa [Nat.add_assoc] using ih (M.step_stack_bound h hc)

end Steps

theorem Runs.toSteps {g : BitString → ℕ} {c d : M.Config} {t : ℕ}
    (h : M.Runs g c d t) : M.Steps g c d t := by
  induction h with
  | halt c h => exact Steps.refl c
  | next h tail ih => exact Steps.next h ih

theorem Runs.final_halts {g : BitString → ℕ} {c d : M.Config} {t : ℕ}
    (h : M.Runs g c d t) : M.step g d = none := by
  induction h with
  | halt c h => exact h
  | next h tail ih => exact ih

theorem runs_iff_steps_halt {g : BitString → ℕ} {c d : M.Config} {t : ℕ} :
    M.Runs g c d t ↔ M.Steps g c d t ∧ M.step g d = none := by
  constructor
  · intro h; exact ⟨h.toSteps,h.final_halts⟩
  · rintro ⟨h,hd⟩
    simpa using h.thenRun (Runs.halt d hd)

end HiddenCircuits.Complexity.OracleMachine
