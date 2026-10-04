import HiddenCircuits.Complexity.OracleElimination.TM2Inlining

/-! A concrete finite TM2 that replaces every query instruction by a call to
an arbitrary binary-output finite TM2. Copying, restoration, output replacement,
and final cleanup are explicit machine instructions. -/
namespace HiddenCircuits.Complexity.OracleElimination
open Turing.TM2

inductive Label (k q : ℕ) (Λ : Type)
  | outer (pc : Fin q)
  | inputRev (i o : Fin k) (next : Fin q)
  | inputCopy (i o : Fin k) (next : Fin q)
  | inner (o : Fin k) (next : Fin q) (pc : Λ)
  | clearOutput (o : Fin k) (next : Fin q)
  | outputRev (o : Fin k) (next : Fin q)
  | outputCopy (o : Fin k) (next : Fin q)
  | clean (j : Fin (k+1))
  deriving Fintype

variable (M : OracleMachine) {f : BitString → BitString}
variable (N : Turing.TM2ComputableInPolyTime id id f)

abbrev Public := Fin M.stackCount ⊕ Unit
abbrev Stack := Public M ⊕ N.tm.K
abbrev Symbol := Alphabet (fun _ : Public M => Bool) N.tm.Γ
abbrev Control := Label M.stackCount M.labelCount N.tm.Λ
abbrev Register := N.tm.σ × Option Bool
abbrev Store := ∀ k : Stack M N,List (Symbol M N k)
abbrev Cfg := Turing.TM2.Cfg (Symbol M N) (Control M N) (Register N)

def caller (i : Fin M.stackCount) : Stack M N := .inl (.inl i)
def scratch : Stack M N := .inl (.inr ())
def privateStack (k : N.tm.K) : Stack M N := .inr k

def initialRegister : Register N := (N.tm.initialState,none)
def resetGoto (l : Control M N) : Stmt (Symbol M N) (Control M N) (Register N) :=
  .load (fun _ => initialRegister N) (.goto (fun _ => l))

def innerLabel (o : Fin M.stackCount) (next : Fin M.labelCount) : Option N.tm.Λ → Control M N
  | none => .clearOutput o next
  | some l => .inner o next l

/-- Branch on a bit pop. Every branch resets the temporary register before
returning to ordinary source execution. -/
def popOuter (i : Fin M.stackCount) (empty zero one : Fin M.labelCount) :
    Stmt (Symbol M N) (Control M N) (Register N) :=
  .pop (caller M N i) (fun v b => (v.1,b))
    (.branch (fun v => v.2.isNone) (resetGoto M N (.outer empty))
      (.branch (fun v => v.2.getD false) (resetGoto M N (.outer one))
        (resetGoto M N (.outer zero))))

/-- Each label is finite and each body contains only finitely many primitive
stack operations and finite-register functions. -/
def code : Control M N → Stmt (Symbol M N) (Control M N) (Register N)
  | .outer pc => match M.code pc with
    | .halt => .goto (fun _ => .clean 0)
    | .jump next => resetGoto M N (.outer next)
    | .push i bit next => .push (caller M N i) (fun _ => bit) (resetGoto M N (.outer next))
    | .pop i empty zero one => popOuter M N i empty zero one
    | .query i o next => .goto (fun _ => .inputRev i o next)
  | .inputRev i o next =>
    .pop (caller M N i) (fun v b => (v.1,b))
      (.branch (fun v => v.2.isNone) (resetGoto M N (.inputCopy i o next))
        (.push (scratch M N) (fun v => v.2.getD false)
          (resetGoto M N (.inputRev i o next))))
  | .inputCopy i o next =>
    .pop (scratch M N) (fun v b => (v.1,b))
      (.branch (fun v => v.2.isNone) (resetGoto M N (.inner o next N.tm.main))
        (.push (caller M N i) (fun v => v.2.getD false)
          (.push (privateStack M N N.tm.k₀) (fun v => N.inputAlphabet.symm (v.2.getD false))
            (resetGoto M N (.inputCopy i o next)))))
  | .inner o next pc => inline (innerLabel M N o next) (N.tm.m pc)
  | .clearOutput o next =>
    .pop (caller M N o) (fun v b => (v.1,b))
      (.branch (fun v => v.2.isNone) (resetGoto M N (.outputRev o next))
        (resetGoto M N (.clearOutput o next)))
  | .outputRev o next =>
    .pop (privateStack M N N.tm.k₁) (fun v b => (v.1,b.map N.outputAlphabet))
      (.branch (fun v => v.2.isNone) (resetGoto M N (.outputCopy o next))
        (.push (scratch M N) (fun v => v.2.getD false)
          (resetGoto M N (.outputRev o next))))
  | .outputCopy o next =>
    .pop (scratch M N) (fun v b => (v.1,b))
      (.branch (fun v => v.2.isNone) (resetGoto M N (.outer next))
        (.push (caller M N o) (fun v => v.2.getD false)
          (resetGoto M N (.outputCopy o next))))
  | .clean j =>
    if h : j.val < M.stackCount then
      if (⟨j.val,h⟩ : Fin M.stackCount) = M.output then
        .goto (fun _ => .clean ⟨j.val+1,by omega⟩)
      else
        .pop (caller M N ⟨j.val,h⟩) (fun v b => (v.1,b))
          (.branch (fun v => v.2.isNone) (resetGoto M N (.clean ⟨j.val+1,by omega⟩))
            (resetGoto M N (.clean j)))
    else .load (fun _ => initialRegister N) .halt

noncomputable def machine : Turing.FinTM2 := by
  letI := N.tm.kFin
  letI := N.tm.ΛFin
  letI := N.tm.σFin
  exact {
    K := Stack M N
    k₀ := caller M N M.input
    k₁ := caller M N M.output
    Γ := Symbol M N
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    Λ := Control M N
    main := .outer M.start
    σ := Register N
    initialState := initialRegister N
    m := code M N }

end HiddenCircuits.Complexity.OracleElimination
