import HiddenCircuits.Complexity.OracleCopyProgram
import HiddenCircuits.Complexity.SharpP

/-! Actual finite bit-stack parsing of the self-delimiting paired input. -/
namespace HiddenCircuits.Complexity.GraphVerifier

structure ParseResult where
  left : BitString
  right : BitString
  ok : Bool
  deriving Repr, DecidableEq

def parse : BitString → ParseResult
  | [] => ⟨[],[],false⟩
  | false::xs => ⟨[],xs,true⟩
  | true::[] => ⟨[],[],false⟩
  | true::b::xs => let r := parse xs; ⟨b::r.left,r.right,r.ok⟩

def parseCost : BitString → ℕ
  | [] => 2
  | false::_ => 2
  | true::[] => 3
  | true::_::xs => 3+parseCost xs

def unpairMachine : OracleMachine where
  stackCount := 4
  labelCount := 10
  input := 0
  output := 3
  start := 0
  code q :=
    if q=0 then .pop 0 8 7 1
    else if q=1 then .pop 0 8 2 3
    else if q=2 then .push 2 false 0
    else if q=3 then .push 2 true 0
    else if q=4 then .pop 2 9 5 6
    else if q=5 then .push 1 false 4
    else if q=6 then .push 1 true 4
    else if q=7 then .push 3 true 4
    else if q=8 then .push 3 false 4
    else .halt

def config (q : Fin 10) (source left temporary flag : BitString) : unpairMachine.Config :=
  ⟨q,Fin.cases source (Fin.cases left (Fin.cases temporary (fun _ => flag)))⟩

private theorem pop_empty (g : BitString → ℕ) (l t f : BitString) :
    unpairMachine.step g (config 0 [] l t f)=some (config 8 [] l t f,1) := rfl
private theorem pop_marker (g : BitString → ℕ) (b : Bool) (xs l t f : BitString) :
    unpairMachine.step g (config 0 (b::xs) l t f)=some (config (if b then 1 else 7) xs l t f,1) := by
  cases b <;> apply congrArg (fun c : unpairMachine.Config => some (c,1)) <;> apply OracleConfig.ext
  all_goals first | rfl | (intro i;fin_cases i <;> rfl)
private theorem pop_value_empty (g : BitString → ℕ) (l t f : BitString) :
    unpairMachine.step g (config 1 [] l t f)=some (config 8 [] l t f,1) := rfl
private theorem pop_value (g : BitString → ℕ) (b : Bool) (xs l t f : BitString) :
    unpairMachine.step g (config 1 (b::xs) l t f)=some (config (if b then 3 else 2) xs l t f,1) := by
  cases b <;> apply congrArg (fun c : unpairMachine.Config => some (c,1)) <;> apply OracleConfig.ext
  all_goals first | rfl | (intro i;fin_cases i <;> rfl)
private theorem push_value (g : BitString → ℕ) (b : Bool) (xs l t f : BitString) :
    unpairMachine.step g (config (if b then 3 else 2) xs l t f)=some (config 0 xs l (b::t) f,1) := by
  cases b <;> apply congrArg (fun c : unpairMachine.Config => some (c,1)) <;> apply OracleConfig.ext
  all_goals first | rfl | (intro i;fin_cases i <;> rfl)
private theorem push_flag (g : BitString → ℕ) (b : Bool) (xs l t f : BitString) :
    unpairMachine.step g (config (if b then 7 else 8) xs l t f)=some (config 4 xs l t (b::f),1) := by
  cases b <;> apply congrArg (fun c : unpairMachine.Config => some (c,1)) <;> apply OracleConfig.ext
  all_goals first | rfl | (intro i;fin_cases i <;> rfl)

theorem parse_steps (g : BitString → ℕ) (xs l t f : BitString) :
    unpairMachine.Steps g (config 0 xs l t f)
      (config 4 (parse xs).right l ((parse xs).left.reverse++t) ((parse xs).ok::f))
      (parseCost xs) := by
  cases xs with
  | nil =>
    exact (OracleMachine.Steps.single (pop_empty g l t f)).trans
      (OracleMachine.Steps.single (push_flag g false [] l t f))
  | cons b xs =>
    cases b with
    | false =>
      exact (OracleMachine.Steps.single (pop_marker g false xs l t f)).trans
        (OracleMachine.Steps.single (push_flag g true xs l t f))
    | true =>
      cases xs with
      | nil =>
        exact (OracleMachine.Steps.single (pop_marker g true [] l t f)).trans
          ((OracleMachine.Steps.single (pop_value_empty g l t f)).trans
            (OracleMachine.Steps.single (push_flag g false [] l t f)))
      | cons b xs =>
        have h := (OracleMachine.Steps.single (pop_marker g true (b::xs) l t f)).trans
          ((OracleMachine.Steps.single (pop_value g b xs l t f)).trans
            ((OracleMachine.Steps.single (push_value g b xs l t f)).trans
              (parse_steps g xs l (b::t) f)))
        convert h using 1 <;> simp [parse,parseCost,List.reverse_cons,List.append_assoc] <;> omega
termination_by xs.length

private theorem reverse_empty (g : BitString → ℕ) (xs l f : BitString) :
    unpairMachine.step g (config 4 xs l [] f)=some (config 9 xs l [] f,1) := rfl
private theorem reverse_pop (g : BitString → ℕ) (b : Bool) (xs l t f : BitString) :
    unpairMachine.step g (config 4 xs l (b::t) f)=some (config (if b then 6 else 5) xs l t f,1) := by
  cases b <;> apply congrArg (fun c : unpairMachine.Config => some (c,1)) <;> apply OracleConfig.ext
  all_goals first | rfl | (intro i;fin_cases i <;> rfl)
private theorem reverse_push (g : BitString → ℕ) (b : Bool) (xs l t f : BitString) :
    unpairMachine.step g (config (if b then 6 else 5) xs l t f)=some (config 4 xs (b::l) t f,1) := by
  cases b <;> apply congrArg (fun c : unpairMachine.Config => some (c,1)) <;> apply OracleConfig.ext
  all_goals first | rfl | (intro i;fin_cases i <;> rfl)

theorem reverse_steps (g : BitString → ℕ) (xs l t f : BitString) :
    unpairMachine.Steps g (config 4 xs l t f) (config 9 xs (t.reverse++l) [] f) (2*t.length+1) := by
  induction t generalizing l with
  | nil => exact OracleMachine.Steps.single (reverse_empty g xs l f)
  | cons b t ih =>
    have h := (OracleMachine.Steps.single (reverse_pop g b xs l t f)).trans
      ((OracleMachine.Steps.single (reverse_push g b xs l t f)).trans (ih (b::l)))
    convert h using 1
    · simp [List.reverse_cons,List.append_assoc]
    · simp; omega

theorem unpair_runs (g : BitString → ℕ) (xs : BitString) :
    unpairMachine.Runs g (config 0 xs [] [] [])
      (config 9 (parse xs).right (parse xs).left [] [(parse xs).ok])
      (parseCost xs+2*(parse xs).left.length+1) := by
  apply (OracleMachine.runs_iff_steps_halt unpairMachine).mpr
  refine ⟨?_,rfl⟩
  have h := (parse_steps g xs [] [] []).trans
    (reverse_steps g (parse xs).right [] ((parse xs).left.reverse++[]) [(parse xs).ok])
  simpa [Nat.add_assoc] using h


@[simp] theorem parse_pair (x y : BitString) : parse (pairBits x y)=⟨x,y,true⟩ := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [pairBits,parse,ih]

theorem parse_spec (xs : BitString) :
    unpairBits xs=if (parse xs).ok then some ((parse xs).left,(parse xs).right) else none := by
  cases xs with
  | nil => rfl
  | cons b xs =>
    cases b with
    | false => rfl
    | true =>
      cases xs with
      | nil => rfl
      | cons b xs =>
        simp only [unpairBits,parse]
        rw [parse_spec xs]
        cases he : (parse xs).ok <;> simp [he]
termination_by xs.length

theorem unpair_cost_bound (xs : BitString) :
    parseCost xs+2*(parse xs).left.length+1≤3*xs.length+4 := by
  cases xs with
  | nil => simp [parse,parseCost]
  | cons b xs =>
    cases b with
    | false => simp [parse,parseCost]
    | true =>
      cases xs with
      | nil => simp [parse,parseCost]
      | cons b xs =>
        have ih := unpair_cost_bound xs
        simp only [parse,parseCost,List.length_cons]
        omega
termination_by xs.length

theorem unpair_initial (xs : BitString) : unpairMachine.init xs=config 0 xs [] [] [] := by
  apply OracleConfig.ext
  · rfl
  · intro i; fin_cases i <;> rfl

/-- Actual original-order parser, including malformed-input rejection and a linear step bound. -/
theorem unpair_output (g : BitString → ℕ) (xs : BitString) :
    ∃ c : unpairMachine.Config, ∃ cost : ℕ,
      unpairMachine.Runs g (unpairMachine.init xs) c cost ∧ cost≤3*xs.length+4 ∧
      c.stack (0:Fin 4)=(parse xs).right ∧ c.stack (1:Fin 4)=(parse xs).left ∧ c.stack (2:Fin 4)=[] ∧
      c.stack (3:Fin 4)=[(parse xs).ok] := by
  refine ⟨config 9 (parse xs).right (parse xs).left [] [(parse xs).ok],
    parseCost xs+2*(parse xs).left.length+1,?_,unpair_cost_bound xs,rfl,rfl,rfl,rfl⟩
  rw [unpair_initial]
  exact unpair_runs g xs

end HiddenCircuits.Complexity.GraphVerifier
