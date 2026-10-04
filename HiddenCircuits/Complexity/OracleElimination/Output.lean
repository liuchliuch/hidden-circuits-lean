import HiddenCircuits.Complexity.OracleElimination.Input

/-! Physically replace the target stack by the solver's answer and clear its
native output stack. The caller's other stacks are preserved. -/
namespace HiddenCircuits.Complexity.OracleElimination
open Turing.TM2
variable (M : OracleMachine) {f : BitString → BitString}
variable (N : Turing.TM2ComputableInPolyTime id id f)

 theorem clearOutput_eval (o : Fin M.stackCount) (next : Fin M.labelCount)
    (S : SourceStore M) (T : PrivateStore N) (xs : BitString) :
    Eval (machine M N).step
      (atLabel M N (.clearOutput o next) (Function.update S o xs) [] T)
      (atLabel M N (.outputRev o next) (Function.update S o []) [] T)
      (xs.length+1) := by
  induction xs with
  | nil =>
    apply Eval.single
    rw [step_atLabel]
    simp [code,stepAux]
  | cons b bs ih =>
    have hs : (machine M N).step
        (atLabel M N (.clearOutput o next) (Function.update S o (b::bs)) [] T) =
        some (atLabel M N (.clearOutput o next) (Function.update S o bs) [] T) := by
      rw [step_atLabel]
      simp [code,stepAux]
    simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using (Eval.single hs).trans ih

 theorem outputRev_eval (o : Fin M.stackCount) (next : Fin M.labelCount)
    (S : SourceStore M) (T : PrivateStore N) (xs acc : BitString) :
    Eval (machine M N).step
      (atLabel M N (.outputRev o next) S acc
        (Function.update T N.tm.k₁ (xs.map N.outputAlphabet.invFun)))
      (atLabel M N (.outputCopy o next) S (xs.reverse ++ acc)
        (Function.update T N.tm.k₁ []))
      (xs.length+1) := by
  induction xs generalizing acc with
  | nil =>
    apply Eval.single
    rw [step_atLabel]
    simp [code,stepAux]
  | cons b bs ih =>
    have hs : (machine M N).step
        (atLabel M N (.outputRev o next) S acc
          (Function.update T N.tm.k₁ ((b::bs).map N.outputAlphabet.invFun))) =
        some (atLabel M N (.outputRev o next) S (b::acc)
          (Function.update T N.tm.k₁ (bs.map N.outputAlphabet.invFun))) := by
      rw [step_atLabel]
      simp [code,stepAux]
    have h := (Eval.single hs).trans (ih (b::acc))
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

 theorem outputCopy_eval (o : Fin M.stackCount) (next : Fin M.labelCount)
    (S : SourceStore M) (T : PrivateStore N) (xs ys : BitString) :
    Eval (machine M N).step
      (atLabel M N (.outputCopy o next) (Function.update S o ys) xs T)
      (atLabel M N (.outer next) (Function.update S o (xs.reverse ++ ys)) [] T)
      (xs.length+1) := by
  induction xs generalizing ys with
  | nil =>
    apply Eval.single
    rw [step_atLabel]
    simp [code,stepAux]
  | cons b bs ih =>
    have hs : (machine M N).step
        (atLabel M N (.outputCopy o next) (Function.update S o ys) (b::bs) T) =
        some (atLabel M N (.outputCopy o next) (Function.update S o (b::ys)) bs T) := by
      rw [step_atLabel]
      simp [code,stepAux]
    have h := (Eval.single hs).trans (ih (b::ys))
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

 theorem query_output_eval (o : Fin M.stackCount) (next : Fin M.labelCount)
    (S : SourceStore M) (xs : BitString) :
    Eval (machine M N).step
      (atLabel M N (.clearOutput o next) S []
        (Function.update (fun _ => []) N.tm.k₁ (xs.map N.outputAlphabet.invFun)))
      (atSource M N ⟨next,Function.update S o xs⟩)
      ((S o).length+2*xs.length+3) := by
  have h1 := clearOutput_eval M N o next S
    (Function.update (fun _ => []) N.tm.k₁ (xs.map N.outputAlphabet.invFun)) (S o)
  have h2 := outputRev_eval M N o next (Function.update S o []) (fun _ => []) xs []
  have h3 := outputCopy_eval M N o next S (fun _ => []) xs.reverse []
  have he : Function.update (fun k : N.tm.K => ([] : List (N.tm.Γ k))) N.tm.k₁ [] =
      (fun k : N.tm.K => ([] : List (N.tm.Γ k))) := by
    funext k;simp [Function.update_apply]
  rw [he] at h2
  have h := (h1.trans h2).trans (by simpa using h3)
  simpa [atSource,Nat.two_mul,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

 theorem query_eval (i o : Fin M.stackCount) (next : Fin M.labelCount) (S : SourceStore M) :
    Eval (machine M N).step
      (atLabel M N (.inputRev i o next) S [] (fun _ => []))
      (atSource M N ⟨next,Function.update S o (f (S i))⟩)
      (2*(S i).length+(S o).length+2*(f (S i)).length+N.time.eval (S i).length+5) := by
  have h1 := query_input_eval M N i o next S
  have h2 := solver_eval M N o next S (S i)
  have h3 := query_output_eval M N o next S (f (S i))
  apply ((h1.trans h2).trans h3).mono
  omega

end HiddenCircuits.Complexity.OracleElimination
