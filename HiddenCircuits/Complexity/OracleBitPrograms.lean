import HiddenCircuits.Complexity.OracleExecution

/-! Concrete finite bit-stack programs with operational correctness and exact
charged running times, used by the emitter compiler. -/
namespace HiddenCircuits.Complexity

@[ext] theorem OracleConfig.ext {k q : ℕ} {c d : OracleConfig k q}
    (hpc : c.pc = d.pc) (hs : ∀ i, c.stack i = d.stack i) : c = d := by
  cases c
  cases d
  congr 1
  exact funext hs

namespace BitPrograms

/-- Move all bits from stack0 to stack1, reversing their order. -/
def reverseMachine : OracleMachine where
  stackCount := 2
  labelCount := 4
  input := 0
  output := 1
  start := 0
  code q := if q = 0 then .pop 0 3 1 2
    else if q = 1 then .push 1 false 0
    else if q = 2 then .push 1 true 0
    else .halt

def reverseConfig (q : Fin 4) (source target : BitString) : reverseMachine.Config :=
  ⟨q,Fin.cases source (fun _ => target)⟩

lemma reverse_pop_nil (g : BitString → ℕ) (target : BitString) :
    reverseMachine.step g (reverseConfig 0 [] target) = some (reverseConfig 3 [] target,1) := rfl

lemma reverse_pop_cons (g : BitString → ℕ) (b : Bool) (source target : BitString) :
    reverseMachine.step g (reverseConfig 0 (b::source) target) =
      some (reverseConfig (if b then 2 else 1) source target,1) := by
  cases b <;> apply congrArg (fun c : reverseMachine.Config => some (c,1)) <;>
    apply OracleConfig.ext
  all_goals first | rfl | (intro i; fin_cases i <;> rfl)

lemma reverse_push (g : BitString → ℕ) (b : Bool) (source target : BitString) :
    reverseMachine.step g (reverseConfig (if b then 2 else 1) source target) =
      some (reverseConfig 0 source (b::target),1) := by
  cases b <;> apply congrArg (fun c : reverseMachine.Config => some (c,1)) <;>
    apply OracleConfig.ext
  all_goals first | rfl | (intro i; fin_cases i <;> rfl)

lemma reverse_halt (g : BitString → ℕ) (target : BitString) :
    reverseMachine.step g (reverseConfig 3 [] target) = none := rfl

/-- Each bit costs exactly one pop and one push, plus the terminal empty test. -/
theorem reverse_steps (g : BitString → ℕ) (source target : BitString) :
    reverseMachine.Steps g (reverseConfig 0 source target)
      (reverseConfig 3 [] (source.reverse++target)) (2*source.length+1) := by
  induction source generalizing target with
  | nil => exact OracleMachine.Steps.single (reverse_pop_nil g target)
  | cons b source ih =>
    have hp := OracleMachine.Steps.single (reverse_pop_cons g b source target)
    have hq := OracleMachine.Steps.single (reverse_push g b source target)
    have hr := ih (b::target)
    convert hp.trans (hq.trans hr) using 1
    · simp [List.reverse_cons,List.append_assoc]
    · simp;omega

/-- Full terminating execution of the real four-label program. -/
theorem reverse_runs (g : BitString → ℕ) (source target : BitString) :
    reverseMachine.Runs g (reverseConfig 0 source target)
      (reverseConfig 3 [] (source.reverse++target)) (2*source.length+1) :=
  (OracleMachine.runs_iff_steps_halt reverseMachine).mpr
    ⟨reverse_steps g source target,reverse_halt g _⟩

lemma reverse_initial (source : BitString) : reverseMachine.init source = reverseConfig 0 source [] := by
  apply OracleConfig.ext
  · rfl
  · intro i
    fin_cases i <;> rfl

/-- Reversal is witnessed by actual finite-machine execution with a linear cost. -/
theorem reverse_binary_output (g : BitString → ℕ) (source : BitString) :
    ∃ c : reverseMachine.Config, reverseMachine.Runs g (reverseMachine.init source) c (2*source.length+1) ∧
      c.stack reverseMachine.output = source.reverse := by
  refine ⟨reverseConfig 3 [] source.reverse,?_,rfl⟩
  rw [reverse_initial]
  simpa using reverse_runs g source []

end BitPrograms
end HiddenCircuits.Complexity
