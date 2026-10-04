import HiddenCircuits.Complexity.GraphVerifier.PairScanSemantics

/-! A constant-state exactly-one row recognizer, independent of row length. -/
namespace HiddenCircuits.Complexity.GraphVerifier.MatchingRuntime

inductive RowState | zero | one | many
  deriving DecidableEq, Fintype

def rowStep : RowState → Bool → RowState
  | q,false => q
  | .zero,true => .one
  | _,true => .many

def rowValue : RowState → ℕ | .zero => 0 | .one => 1 | .many => 2

def rowFold : List Bool → RowState → RowState
  | [],q => q
  | b::bs,q => rowFold bs (rowStep q b)

theorem rowStep_value (q : RowState) (b : Bool) :
    rowValue (rowStep q b)=min 2 (rowValue q+if b then 1 else 0) := by
  cases q <;> cases b <;> rfl

theorem rowFold_value (xs : List Bool) (q : RowState) :
    rowValue (rowFold xs q)=min 2 (rowValue q+xs.count true) := by
  induction xs generalizing q with
  | nil => cases q <;> rfl
  | cons b xs ih =>
    rw [rowFold,ih,rowStep_value]
    cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true,List.count_cons,beq_self_eq_true]
    all_goals norm_num
    all_goals omega

theorem rowFold_one_iff (xs : List Bool) : rowFold xs .zero=.one ↔ xs.count true=1 := by
  have hv := rowFold_value xs .zero
  cases hq : rowFold xs .zero <;> simp [hq,rowValue] at hv ⊢ <;> omega

end HiddenCircuits.Complexity.GraphVerifier.MatchingRuntime
