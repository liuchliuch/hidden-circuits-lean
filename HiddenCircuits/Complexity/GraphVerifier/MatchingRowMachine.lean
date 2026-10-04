import HiddenCircuits.Complexity.GraphVerifier.MatchingRowState
import HiddenCircuits.Complexity.GraphVerifier.RuntimeLibrary

/-! A real constant-state bit machine checks exactly one selected entry in a row. -/
namespace HiddenCircuits.Complexity.GraphVerifier.MatchingRuntime
open OracleBlock OracleMachine

inductive RowControl
  | start | read (q : RowState) (valid : Bool) | bit (q : RowState) (valid : Bool)
  | emit (valid : Bool) | halt
  deriving DecidableEq, Fintype
noncomputable def rowLabel : RowControl ≃ Fin (Fintype.card RowControl) := Fintype.equivFin _
noncomputable def rowCode : RowControl → OracleInstr 3 (Fintype.card RowControl)
  | .start => .pop 2 (rowLabel (.emit false)) (rowLabel (.read .zero false)) (rowLabel (.read .zero true))
  | .read q a => .pop 0 (rowLabel (.emit (a && decide (q=.one)))) (rowLabel (.bit q a)) (rowLabel (.bit q a))
  | .bit q a => .pop 1 (rowLabel (.read .many false)) (rowLabel (.read (rowStep q false) a)) (rowLabel (.read (rowStep q true) a))
  | .emit a => .push 2 a (rowLabel .halt)
  | .halt => .halt
noncomputable abbrev rowMachine : OracleMachine where
  stackCount := 3
  labelCount := Fintype.card RowControl
  input := 0
  output := 0
  start := rowLabel .start
  code q := rowCode (rowLabel.symm q)

def rowMachineStore (clock data flag : BitString) : Store 2 :=
  fun i => if i.val=0 then clock else if i.val=1 then data else flag
noncomputable def rowConfig (q : RowControl) (clock data flag : BitString) : rowMachine.Config :=
  ⟨rowLabel q,rowMachineStore clock data flag⟩

lemma row_start (g : BitString → ℕ) (a : Bool) (clock data f : BitString) :
    rowMachine.step g (rowConfig .start clock data (a::f))=
      some (rowConfig (.read .zero a) clock data f,1) := by
  cases a <;> simp only [OracleMachine.step,rowConfig,rowMachineStore,rowMachine,Equiv.symm_apply_apply,rowCode,Bool.false_eq_true,ite_false,ite_true]
  all_goals apply congrArg (fun d : rowMachine.Config => some (d,1));apply OracleConfig.ext
  all_goals first | rfl | (intro i;fin_cases i <;> rfl)
lemma row_read_empty (g : BitString → ℕ) (q : RowState) (a : Bool) (data f : BitString) :
    rowMachine.step g (rowConfig (.read q a) [] data f)=
      some (rowConfig (.emit (a && decide (q=.one))) [] data f,1) := by
  simp [OracleMachine.step,rowConfig,rowMachineStore,rowMachine,rowCode]
lemma row_read_cons (g : BitString → ℕ) (q : RowState) (a c : Bool) (clock data f : BitString) :
    rowMachine.step g (rowConfig (.read q a) (c::clock) data f)=
      some (rowConfig (.bit q a) clock data f,1) := by
  cases c <;> simp only [OracleMachine.step,rowConfig,rowMachineStore,rowMachine,Equiv.symm_apply_apply,rowCode,Bool.false_eq_true,ite_false,ite_true]
  all_goals apply congrArg (fun d : rowMachine.Config => some (d,1));apply OracleConfig.ext
  all_goals first | rfl | (intro i;fin_cases i <;> rfl)
lemma row_read_bit (g : BitString → ℕ) (q : RowState) (a b : Bool) (clock data f : BitString) :
    rowMachine.step g (rowConfig (.bit q a) clock (b::data) f)=
      some (rowConfig (.read (rowStep q b) a) clock data f,1) := by
  cases b <;> simp only [OracleMachine.step,rowConfig,rowMachineStore,rowMachine,Equiv.symm_apply_apply,rowCode,Bool.false_eq_true,ite_false,ite_true]
  all_goals apply congrArg (fun d : rowMachine.Config => some (d,1));apply OracleConfig.ext
  all_goals first | rfl | (intro i;fin_cases i <;> rfl)
lemma row_emit (g : BitString → ℕ) (a : Bool) (clock data f : BitString) :
    rowMachine.step g (rowConfig (.emit a) clock data f)=some (rowConfig .halt clock data (a::f),1) := by
  simp only [OracleMachine.step,rowConfig,rowMachineStore,rowMachine,Equiv.symm_apply_apply,rowCode]
  apply congrArg (fun d : rowMachine.Config => some (d,1));apply OracleConfig.ext
  · rfl
  · intro i;fin_cases i <;> rfl

 theorem row_scan_steps (g : BitString → ℕ) (clock data f : BitString) (q : RowState) (a : Bool)
    (hlen : clock.length≤data.length) :
    rowMachine.Steps g (rowConfig (.read q a) clock data f)
      (rowConfig .halt [] (data.drop clock.length)
        ((a && decide (rowFold (data.take clock.length) q=.one))::f)) (2*clock.length+2) := by
  induction clock generalizing data q with
  | nil =>
    simpa [rowFold] using (Steps.single (row_read_empty g q a data f)).trans
      (Steps.single (row_emit g (a && decide (q=.one)) [] data f))
  | cons c clock ih =>
    cases data with
    | nil => simp at hlen
    | cons b data =>
      have hh := (Steps.single (row_read_cons g q a c clock (b::data) f)).trans
        ((Steps.single (row_read_bit g q a b clock data f)).trans
          (ih data (rowStep q b) (by simp at hlen;omega)))
      convert hh using 1 <;> simp [rowFold,List.take_succ_cons,List.drop_succ_cons] <;> omega

noncomputable def oneRowBlock : OracleBlock 2 where
  labelCount := Fintype.card RowControl
  start := rowLabel .start
  exit := rowLabel .halt
  code q := rowCode (rowLabel.symm q)
  exit_halt := by simp [rowCode]

/-- Exactly two bit pops per row entry, plus entry/exit instructions. -/
theorem oneRow_executes (g : BitString → ℕ) (clock data : BitString) (a : Bool)
    (hlen : clock.length≤data.length) :
    oneRowBlock.Executes g (rowMachineStore clock data [a])
      (rowMachineStore [] (data.drop clock.length) [a && decide ((data.take clock.length).count true=1)])
      (2*clock.length+3) := by
  have hh := (Steps.single (row_start g a clock data [])).trans (row_scan_steps g clock data [] .zero a hlen)
  have he : decide (rowFold (data.take clock.length) .zero=.one)=decide ((data.take clock.length).count true=1) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using rowFold_one_iff (data.take clock.length)
  rw [he] at hh
  convert hh using 1 <;> omega

 theorem oneRow_queryFree : oneRowBlock.QueryFree := by
  intro q i o next
  change rowCode (rowLabel.symm q)≠.query i o next
  cases rowLabel.symm q <;> simp [rowCode]

end HiddenCircuits.Complexity.GraphVerifier.MatchingRuntime
