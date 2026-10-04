import HiddenCircuits.Circuit.ConstraintPrograms
import HiddenCircuits.Circuit.ConcatAssignments
import HiddenCircuits.Circuit.IndependentIndicator

namespace HiddenCircuits.Circuit

/-- The actual global wire index of a local coordinate of a placed gate. -/
def Placement.activeTrack {n d : ℕ} (p : Placement n d) (i : Fin d) : Fin n :=
  ⟨p.before+i.val,by have hp:=p.size;have hi:=i.isLt;omega⟩

/-- Boolean assignment values in the active region are the literal shifted global coordinates. -/
theorem Placement.active_assignment {n d : ℕ} (p : Placement n d) (x : CodeBits n) (i : Fin d) :
    bitsToAssignment d (p.equiv.symm x).2.1 i = bitsToAssignment n x (p.activeTrack i) := by
  obtain ⟨⟨a,⟨u,c⟩⟩,rfl⟩ := p.equiv.surjective x
  rw [Equiv.symm_apply_apply]
  rw [← bitAt_eq_assignment,← bitAt_eq_assignment]
  change bitAt d u i.val = bitAt n (cast (congrArg CodeBits p.size)
    (codeConcat p.before (d+p.after) a (codeConcat d p.after u c))) (p.before+i.val)
  rw [bitAt_cast p.size,bitAt_concat,if_neg (by omega),Nat.add_sub_cancel_left,bitAt_concat,if_pos i.isLt]

/-- Literal N/CZ entries depend only on whether the two active bits are both one. -/
theorem logicalConstraint_indicator (z : ℚ) : logicalConstraint z=Matrix.diagonal
    (fun x : CodeBits 2 => if bitsToAssignment 2 x 0=true ∧ bitsToAssignment 2 x 1=true then z else 1) := by
  rw [logicalConstraint,constraintDiagonal,reindex_diagonal]
  congr 1
  funext x
  obtain ⟨a,rfl⟩ := twoBitEquiv.surjective x
  fin_cases a <;> rfl

/-- Every placed constraint reads precisely its two actual adjacent wire positions. -/
theorem Placement.constraint_diagonal {n : ℕ} (p : Placement n 2) (z : ℚ) :
    p.lift (logicalConstraint z)=Matrix.diagonal (fun x : CodeBits n =>
      if bitsToAssignment n x (p.activeTrack 0)=true ∧ bitsToAssignment n x (p.activeTrack 1)=true then z else 1) := by
  rw [logicalConstraint_indicator,p.lift_diagonal]
  congr 1
  funext x
  rw [p.active_assignment,p.active_assignment]

/-- The adjacent N gate is the exact graph-edge penalty on its two positions. -/
theorem adjacent_forbid_diagonal {n : ℕ} (i : Fin (n-1)) :
    (ConstraintGate.forbid (adjacentPlacement i)).matrix = Matrix.diagonal
      (edgePenalty ((adjacentPlacement i).activeTrack 0) ((adjacentPlacement i).activeTrack 1)) := by
  exact (adjacentPlacement i).constraint_diagonal 0

end HiddenCircuits.Circuit
