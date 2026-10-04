import HiddenCircuits.Complexity.OracleElimination.Stores

/-! The query's bit string is copied into the solver's native input alphabet,
while preserving the caller's input stack and restoring the scratch stack. -/
namespace HiddenCircuits.Complexity.OracleElimination
open Turing.TM2
variable (M : OracleMachine) {f : BitString → BitString}
variable (N : Turing.TM2ComputableInPolyTime id id f)

 theorem inputRev_eval (i o : Fin M.stackCount) (next : Fin M.labelCount)
    (S : SourceStore M) (T : PrivateStore N) (xs acc : BitString) :
    Eval (machine M N).step
      (atLabel M N (.inputRev i o next) (Function.update S i xs) acc T)
      (atLabel M N (.inputCopy i o next) (Function.update S i []) (xs.reverse ++ acc) T)
      (xs.length+1) := by
  induction xs generalizing acc with
  | nil =>
    apply Eval.single
    rw [step_atLabel]
    simp [code,stepAux]
  | cons b bs ih =>
    have hs : (machine M N).step
        (atLabel M N (.inputRev i o next) (Function.update S i (b::bs)) acc T) =
        some (atLabel M N (.inputRev i o next) (Function.update S i bs) (b::acc) T) := by
      rw [step_atLabel]
      simp [code,stepAux]
    have h := (Eval.single hs).trans (ih (b::acc))
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

 theorem inputCopy_eval (i o : Fin M.stackCount) (next : Fin M.labelCount)
    (S : SourceStore M) (T : PrivateStore N) (xs ys : BitString)
    (zs : List (N.tm.Γ N.tm.k₀)) :
    Eval (machine M N).step
      (atLabel M N (.inputCopy i o next) (Function.update S i ys) xs
        (Function.update T N.tm.k₀ zs))
      (atLabel M N (.inner o next N.tm.main) (Function.update S i (xs.reverse ++ ys)) []
        (Function.update T N.tm.k₀ (xs.reverse.map N.inputAlphabet.invFun ++ zs)))
      (xs.length+1) := by
  induction xs generalizing ys zs with
  | nil =>
    apply Eval.single
    rw [step_atLabel]
    simp [code,stepAux]
  | cons b bs ih =>
    have hs : (machine M N).step
        (atLabel M N (.inputCopy i o next) (Function.update S i ys) (b::bs)
          (Function.update T N.tm.k₀ zs)) =
        some (atLabel M N (.inputCopy i o next) (Function.update S i (b::ys)) bs
          (Function.update T N.tm.k₀ (N.inputAlphabet.invFun b :: zs))) := by
      rw [step_atLabel]
      simp [code,stepAux]
    have h := (Eval.single hs).trans (ih (b::ys) (N.inputAlphabet.invFun b :: zs))
    simpa [List.reverse_cons,List.append_assoc,List.map_append,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

 theorem private_init_store (x : BitString) :
    (Turing.initList N.tm (x.map N.inputAlphabet.invFun)).stk =
      Function.update (fun _ => []) N.tm.k₀ (x.map N.inputAlphabet.invFun) := by
  funext k
  by_cases h : k = N.tm.k₀
  · subst k;simp [Turing.initList]
  · simp [Turing.initList,Function.update_of_ne h,h]

 theorem private_halt_store (x : BitString) :
    (Turing.haltList N.tm (x.map N.outputAlphabet.invFun)).stk =
      Function.update (fun _ => []) N.tm.k₁ (x.map N.outputAlphabet.invFun) := by
  funext k
  by_cases h : k = N.tm.k₁
  · subst k;simp [Turing.haltList]
  · simp [Turing.haltList,Function.update_of_ne h,h]

 theorem query_input_eval (i o : Fin M.stackCount) (next : Fin M.labelCount)
    (S : SourceStore M) :
    Eval (machine M N).step
      (atLabel M N (.inputRev i o next) S [] (fun _ => []))
      (config (innerLabel M N o next) (publicStore M S []) none
        (Turing.initList N.tm ((S i).map N.inputAlphabet.invFun)))
      (2*(S i).length+2) := by
  have h1 := inputRev_eval M N i o next S (fun _ => []) (S i) []
  have h2 := inputCopy_eval M N i o next S (fun _ => []) (S i).reverse [] []
  have he : Function.update (fun k : N.tm.K => ([] : List (N.tm.Γ k))) N.tm.k₀ [] =
      (fun k : N.tm.K => ([] : List (N.tm.Γ k))) := by
    funext k;simp [Function.update_apply]
  rw [he] at h2
  have h := h1.trans (by simpa using h2)
  have hout : atLabel M N (.inner o next N.tm.main) S []
      (Function.update (fun _ => []) N.tm.k₀ ((S i).map N.inputAlphabet.invFun)) =
      config (innerLabel M N o next) (publicStore M S []) none
        (Turing.initList N.tm ((S i).map N.inputAlphabet.invFun)) := by
    apply OracleMachine.tm2Cfg_ext
    · rfl
    · rfl
    · dsimp only [atLabel,config,fullStore]
      rw [private_init_store]
  rw [←hout]
  simpa [Nat.mul_add,Nat.two_mul,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

 theorem solver_eval (o : Fin M.stackCount) (next : Fin M.labelCount)
    (S : SourceStore M) (x : BitString) :
    Eval (machine M N).step
      (config (innerLabel M N o next) (publicStore M S []) none
        (Turing.initList N.tm (x.map N.inputAlphabet.invFun)))
      (atLabel M N (.clearOutput o next) S []
        (Function.update (fun _ => []) N.tm.k₁ ((f x).map N.outputAlphabet.invFun)))
      (N.time.eval x.length) := by
  have h : Eval N.tm.step (Turing.initList N.tm (x.map N.inputAlphabet.invFun))
      (Turing.haltList N.tm ((f x).map N.outputAlphabet.invFun)) (N.time.eval x.length) :=
    ⟨N.outputsFun x⟩
  have hh := inline_eval N.tm.m (code M N) (innerLabel M N o next)
    (fun _ => rfl) (publicStore M S []) none h
  have hout : config (innerLabel M N o next) (publicStore M S []) none
      (Turing.haltList N.tm ((f x).map N.outputAlphabet.invFun)) =
      atLabel M N (.clearOutput o next) S []
        (Function.update (fun _ => []) N.tm.k₁ ((f x).map N.outputAlphabet.invFun)) := by
    apply OracleMachine.tm2Cfg_ext
    · rfl
    · rfl
    · dsimp only [atLabel,config,fullStore]
      rw [private_halt_store]
  rw [hout] at hh
  exact hh

end HiddenCircuits.Complexity.OracleElimination
