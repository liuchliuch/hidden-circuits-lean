import HiddenCircuits.Complexity.OracleElimination.Output
import HiddenCircuits.Complexity.OracleElimination.Cleanup
import HiddenCircuits.Complexity.FP

/-! Polynomial simulation of every charged oracle execution, with all query
arguments and answers accounted for by the source's operational cost. -/
namespace HiddenCircuits.Complexity.OracleElimination
open Turing.TM2 Polynomial
variable (M : OracleMachine) {g : BitString → ℕ}
variable (N : Turing.TM2ComputableInPolyTime id id (fun x => Computability.encodeNat (g x)))

def allowance (n : ℕ) : ℕ := 5*n+N.time.eval n+6

 theorem allowance_mono : Monotone (allowance N) := by
  intro a b h
  have hp := polynomial_nat_eval_mono N.time h
  dsimp only at hp
  dsimp [allowance]
  omega

 theorem ordinary_step {c d : M.Config} {a : ℕ}
    (h : M.step g c = some (d,a))
    (hq : ∀ i o next, M.code c.pc ≠ .query i o next) :
    Eval (machine M N).step (atSource M N c) (atSource M N d) 1 := by
  apply Eval.single
  cases hi : M.code c.pc with
  | halt => simp [OracleMachine.step,hi] at h
  | jump next =>
    simp only [OracleMachine.step,hi] at h
    cases h
    simp only [atSource]
    rw [step_atLabel]
    simp [atSource,code,hi]
  | push i b next =>
    simp only [OracleMachine.step,hi] at h
    cases h
    simp only [atSource]
    rw [step_atLabel]
    simp [atSource,code,hi,stepAux]
  | pop i empty zero one =>
    cases he : c.stack i with
    | nil =>
      simp only [OracleMachine.step,hi,he] at h
      cases h
      simp only [atSource]
      rw [step_atLabel]
      have hu : Function.update c.stack i [] = c.stack := Function.update_eq_self_iff.mpr he.symm
      simp [code,hi,popOuter,stepAux,he,hu]
    | cons b bs =>
      simp only [OracleMachine.step,hi,he] at h
      cases h
      cases b <;> simp only [atSource] <;> rw [step_atLabel] <;> simp [code,hi,popOuter,stepAux,he]
  | query i o next => exact False.elim (hq i o next hi)

 theorem step_eval {c d : M.Config} {a B : ℕ}
    (h : M.step g c = some (d,a)) (hS : ∀ i,(c.stack i).length ≤ B)
    (ha : a ≤ B) :
    Eval (machine M N).step (atSource M N c) (atSource M N d) (a*allowance N B) := by
  have hpos := M.step_cost_positive h
  by_cases hq : ∃ i o next, M.code c.pc = .query i o next
  · obtain ⟨i,o,next,hq⟩ := hq
    simp only [OracleMachine.step,hq] at h
    cases h
    have hs : (machine M N).step (atSource M N c) =
        some (atLabel M N (.inputRev i o next) c.stack [] (fun _ => [])) := by
      simp only [atSource]
      rw [step_atLabel]
      simp [atSource,code,hq,stepAux,atLabel]
    have hr := (Eval.single hs).trans (query_eval M N i o next c.stack)
    apply hr.mono
    have hi := hS i
    have ho := hS o
    have hp := polynomial_nat_eval_mono N.time hi
    have hout : (Computability.encodeNat (g (c.stack i))).length ≤ B := by
      simpa [OracleMachine.answerBits] using (show
        (OracleMachine.answerBits g (c.stack i)).length ≤ B by omega)
    dsimp only at hp
    dsimp [OracleMachine.answerBits] at hpos
    calc
      _ ≤ allowance N B := by dsimp [allowance];omega
      _ ≤ _ := Nat.le_mul_of_pos_left _ hpos

  · apply (ordinary_step M N h (by simpa using hq)).mono
    have hA : 1 ≤ allowance N B := by simp [allowance]
    exact hA.trans (Nat.le_mul_of_pos_left _ hpos)

 theorem runs_eval {c d : M.Config} {t n : ℕ}
    (h : M.Runs g c d t) (hS : ∀ i,(c.stack i).length ≤ n) :
    Eval (machine M N).step (atSource M N c) (atSource M N d)
      (t*allowance N (n+t)) := by
  induction h generalizing n with
  | halt c h => simpa using Eval.refl (machine M N).step (atSource M N c)
  | @next c d e a b hs ht ih =>
    have ha : a ≤ n+(a+b) := by omega
    have hb : ∀ i,(c.stack i).length ≤ n+(a+b) := by intro i;exact (hS i).trans (by omega)
    have hh := step_eval M N hs hb ha
    have hd := M.step_stack_bound hs hS
    have hi := ih hd
    have hsum := hh.trans hi
    simpa [Nat.add_assoc,Nat.add_mul] using hsum

 theorem halt_eval {c : M.Config} {n : ℕ} (h : M.step g c = none)
    (hS : ∀ i,(c.stack i).length ≤ n) :
    Eval (machine M N).step (atSource M N c)
      (Turing.haltList (machine M N) (c.stack M.output)) (M.stackCount*(n+1)+2) := by
  have hc : M.code c.pc = .halt := by
    cases hi : M.code c.pc <;> simp [OracleMachine.step,hi] at h ⊢
    split at h <;> contradiction
  have hs : (machine M N).step (atSource M N c) =
      some (atLabel M N (.clean 0) c.stack [] (fun _ => [])) := by
    simp only [atSource]
    rw [step_atLabel]
    simp [atSource,code,hc,stepAux,atLabel]
  have ht := cleanup_eval M N 0 c.stack n hS
  simp only [Fin.val_zero,Nat.sub_zero] at ht
  rw [halted_output] at ht
  apply ((Eval.single hs).trans ht).mono
  omega

 theorem run_halt {c d : M.Config} {t : ℕ} (h : M.Runs g c d t) : M.step g d = none := by
  induction h with
  | halt c h => exact h
  | next h ht ih => exact ih

 theorem runs_to_output {x : BitString} {d : M.Config} {t : ℕ}
    (h : M.Runs g (M.init x) d t) :
    Eval (machine M N).step (Turing.initList (machine M N) x)
      (Turing.haltList (machine M N) (d.stack M.output))
      (t*allowance N (x.length+t)+M.stackCount*(x.length+t+1)+2) := by
  have h1 := runs_eval M N h (M.init_stack_bound x)
  have h2 := halt_eval M N (run_halt M h) (OracleMachine.Runs.stack_bound M h (M.init_stack_bound x))
  rw [initial_eq]
  simpa [Nat.add_assoc] using h1.trans h2

end HiddenCircuits.Complexity.OracleElimination
