import HiddenCircuits.Complexity.OracleElimination.Machine

namespace HiddenCircuits.Complexity.OracleElimination
open Turing.TM2
variable (M : OracleMachine) {f : BitString → BitString}
variable (N : Turing.TM2ComputableInPolyTime id id f)

abbrev SourceStore := Fin M.stackCount → BitString
abbrev PrivateStore := ∀ k : N.tm.K,List (N.tm.Γ k)

def publicStore (S : SourceStore M) (xs : BitString) : Public M → BitString
  | .inl i => S i
  | .inr _ => xs

def fullStore (S : SourceStore M) (xs : BitString) (T : PrivateStore N) : Store M N :=
  store (publicStore M S xs) T

def atLabel (l : Control M N) (S : SourceStore M) (xs : BitString) (T : PrivateStore N) : Cfg M N :=
  ⟨some l,initialRegister N,fullStore M N S xs T⟩

def atSource (c : M.Config) : Cfg M N := atLabel M N (.outer c.pc) c.stack [] (fun _ => [])

@[simp] theorem fullStore_public (S : SourceStore M) (xs : BitString) (T : PrivateStore N) (i) :
    fullStore M N S xs T (caller M N i) = S i := rfl
@[simp] theorem fullStore_scratch (S : SourceStore M) (xs : BitString) (T : PrivateStore N) :
    fullStore M N S xs T (scratch M N) = xs := rfl
@[simp] theorem fullStore_private (S : SourceStore M) (xs : BitString) (T : PrivateStore N) (i) :
    fullStore M N S xs T (privateStack M N i) = T i := rfl

@[simp] theorem fullStore_update_public (S : SourceStore M) (xs : BitString) (T : PrivateStore N)
    (i : Fin M.stackCount) (ys : BitString) :
    Function.update (fullStore M N S xs T) (caller M N i) ys =
      fullStore M N (Function.update S i ys) xs T := by
  funext k
  cases k with
  | inl a =>
    cases a with
    | inl j =>
      by_cases h : j = i
      · subst j;simp [caller,fullStore,publicStore]
      · simp [caller,fullStore,publicStore,Function.update_apply,h]
    | inr u => simp [caller,fullStore,publicStore,Function.update_apply]
  | inr k => simp [caller,fullStore,Function.update_apply]

@[simp] theorem fullStore_update_scratch (S : SourceStore M) (xs : BitString) (T : PrivateStore N)
    (ys : BitString) :
    Function.update (fullStore M N S xs T) (scratch M N) ys = fullStore M N S ys T := by
  funext k
  cases k with
  | inl a =>
    cases a with
    | inl j => simp [scratch,fullStore,publicStore,Function.update_apply]
    | inr u => cases u;simp [scratch,fullStore,publicStore]
  | inr k => simp [scratch,fullStore,Function.update_apply]

@[simp] theorem fullStore_update_private (S : SourceStore M) (xs : BitString) (T : PrivateStore N)
    (i : N.tm.K) (ys : List (N.tm.Γ i)) :
    Function.update (fullStore M N S xs T) (privateStack M N i) ys =
      fullStore M N S xs (Function.update T i ys) :=
  store_update_right _ _ _ _

@[simp] theorem step_atLabel (l : Control M N) (S : SourceStore M) (xs : BitString) (T : PrivateStore N) :
    (machine M N).step (atLabel M N l S xs T) =
      some (stepAux (code M N l) (initialRegister N) (fullStore M N S xs T)) := rfl

@[simp] theorem resetGoto_step (l : Control M N) (v : Register N)
    (S : SourceStore M) (xs : BitString) (T : PrivateStore N) :
    stepAux (resetGoto M N l) v (fullStore M N S xs T) = atLabel M N l S xs T := rfl

theorem initial_eq (x : BitString) : Turing.initList (machine M N) x = atSource M N (M.init x) := by
  apply OracleMachine.tm2Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl a =>
      cases a with
      | inl i => simp [Turing.initList,machine,caller,atSource,atLabel,fullStore,publicStore,OracleMachine.init,Function.update_apply]
      | inr u => simp [Turing.initList,machine,caller,atSource,atLabel,fullStore,publicStore,OracleMachine.init]
    | inr k => simp [Turing.initList,machine,caller,atSource,atLabel,fullStore,publicStore,OracleMachine.init]

end HiddenCircuits.Complexity.OracleElimination
