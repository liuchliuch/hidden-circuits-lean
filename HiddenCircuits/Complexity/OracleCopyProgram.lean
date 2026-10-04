import HiddenCircuits.Complexity.OracleBitPrograms
import HiddenCircuits.Complexity.OracleEmbedding

/-! An actual nine-label bit-stack copying program. It restores its source,
preserves an existing target suffix, clears its temporary stack, and has exact
linear charged cost. The first phase reuses the verified reversal block. -/
namespace HiddenCircuits.Complexity.BitPrograms

def copyMachine : OracleMachine where
  stackCount := 3
  labelCount := 9
  input := 0
  output := 1
  start := 0
  code q :=
    if q = 0 then .pop 0 3 1 2
    else if q = 1 then .push 2 false 0
    else if q = 2 then .push 2 true 0
    else if q = 3 then .pop 2 8 4 6
    else if q = 4 then .push 0 false 5
    else if q = 5 then .push 1 false 3
    else if q = 6 then .push 0 true 7
    else if q = 7 then .push 1 true 3
    else .halt

def copyConfig (q : Fin 9) (source target temporary : BitString) : copyMachine.Config :=
  ⟨q,Fin.cases source (Fin.cases target (fun _ => temporary))⟩

def reverseToCopyStack : Fin 2 ↪ Fin 3 where
  toFun i := if i = 0 then 0 else 2
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

def reverseToCopyLabel (q : Fin 4) : Fin 9 := q.castLE (by decide)

lemma reverse_embeds_copy : OracleMachine.EmbedsCode reverseMachine copyMachine reverseToCopyStack reverseToCopyLabel := by
  intro q h
  fin_cases q <;> simp [reverseMachine,copyMachine,reverseToCopyStack,reverseToCopyLabel,OracleInstr.map] at *

/-- Embedding preserves the target stack, which is outside the reversal block. -/
theorem copy_first_phase (g : BitString → ℕ) (source target : BitString) :
    copyMachine.Steps g (copyConfig 0 source target [])
      (copyConfig 3 [] target source.reverse) (2*source.length+1) := by
  have hc : OracleMachine.Corresponds reverseMachine copyMachine reverseToCopyStack reverseToCopyLabel
      (reverseConfig 0 source []) (copyConfig 0 source target []) := by
    constructor
    · rfl
    · intro i;fin_cases i <;> rfl
  obtain ⟨d,hd,hcor,hframe⟩ := OracleMachine.steps_embed_frame reverseMachine copyMachine
    reverseToCopyStack reverseToCopyLabel reverse_embeds_copy g hc (reverse_steps g source [])
  have he : d = copyConfig 3 [] target source.reverse := by
    apply OracleConfig.ext
    · exact hcor.1
    · intro i
      fin_cases i
      · exact hcor.2 ⟨0,by decide⟩
      · exact hframe ⟨1,by decide⟩ (by intro j;fin_cases j <;> decide)
      · simpa using hcor.2 ⟨1,by decide⟩
  rwa [he] at hd

lemma copy_second_pop_nil (g : BitString → ℕ) (source target : BitString) :
    copyMachine.step g (copyConfig 3 source target []) = some (copyConfig 8 source target [],1) := rfl

lemma copy_second_pop_cons (g : BitString → ℕ) (b : Bool) (source target temporary : BitString) :
    copyMachine.step g (copyConfig 3 source target (b::temporary)) =
      some (copyConfig (if b then 6 else 4) source target temporary,1) := by
  cases b <;> apply congrArg (fun c : copyMachine.Config => some (c,1)) <;> apply OracleConfig.ext
  all_goals first | rfl | (intro i;fin_cases i <;> rfl)

lemma copy_second_push_source (g : BitString → ℕ) (b : Bool) (source target temporary : BitString) :
    copyMachine.step g (copyConfig (if b then 6 else 4) source target temporary) =
      some (copyConfig (if b then 7 else 5) (b::source) target temporary,1) := by
  cases b <;> apply congrArg (fun c : copyMachine.Config => some (c,1)) <;> apply OracleConfig.ext
  all_goals first | rfl | (intro i;fin_cases i <;> rfl)

lemma copy_second_push_target (g : BitString → ℕ) (b : Bool) (source target temporary : BitString) :
    copyMachine.step g (copyConfig (if b then 7 else 5) source target temporary) =
      some (copyConfig 3 source (b::target) temporary,1) := by
  cases b <;> apply congrArg (fun c : copyMachine.Config => some (c,1)) <;> apply OracleConfig.ext
  all_goals first | rfl | (intro i;fin_cases i <;> rfl)

/-- Pop each temporary bit and push it to both destinations. -/
theorem copy_second_phase (g : BitString → ℕ) (temporary source target : BitString) :
    copyMachine.Steps g (copyConfig 3 source target temporary)
      (copyConfig 8 (temporary.reverse++source) (temporary.reverse++target) []) (3*temporary.length+1) := by
  induction temporary generalizing source target with
  | nil => exact OracleMachine.Steps.single (copy_second_pop_nil g source target)
  | cons b temporary ih =>
    have hp := OracleMachine.Steps.single (copy_second_pop_cons g b source target temporary)
    have hq := OracleMachine.Steps.single (copy_second_push_source g b source target temporary)
    have hr := OracleMachine.Steps.single (copy_second_push_target g b (b::source) target temporary)
    have ht := ih (b::source) (b::target)
    convert hp.trans (hq.trans (hr.trans ht)) using 1
    · simp [List.reverse_cons,List.append_assoc]
    · simp;omega

theorem copy_steps (g : BitString → ℕ) (source target : BitString) :
    copyMachine.Steps g (copyConfig 0 source target [])
      (copyConfig 8 source (source++target) []) (5*source.length+2) := by
  have h := (copy_first_phase g source target).trans (copy_second_phase g source.reverse [] target)
  convert h using 1
  · simp
  · simp;omega

theorem copy_runs (g : BitString → ℕ) (source target : BitString) :
    copyMachine.Runs g (copyConfig 0 source target [])
      (copyConfig 8 source (source++target) []) (5*source.length+2) :=
  (OracleMachine.runs_iff_steps_halt copyMachine).mpr ⟨copy_steps g source target,rfl⟩

lemma copy_initial (source : BitString) : copyMachine.init source = copyConfig 0 source [] [] := by
  apply OracleConfig.ext
  · rfl
  · intro i;fin_cases i <;> rfl

/-- The source is restored and the copied output is exact, with a verified linear runtime. -/
theorem copy_binary_output (g : BitString → ℕ) (source : BitString) :
    ∃ c : copyMachine.Config, copyMachine.Runs g (copyMachine.init source) c (5*source.length+2) ∧
      c.stack copyMachine.input = source ∧ c.stack copyMachine.output = source := by
  refine ⟨copyConfig 8 source source [],?_,rfl,rfl⟩
  rw [copy_initial]
  simpa using copy_runs g source []

end HiddenCircuits.Complexity.BitPrograms
