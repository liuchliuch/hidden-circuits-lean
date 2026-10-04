import HiddenCircuits.Complexity.LocalClauseEmitter
import HiddenCircuits.Complexity.UniformVerifier

/-! The operational local-clause output agrees with the exact local truth-table
constraints used in the count-preserving verifier formula. -/
namespace HiddenCircuits.Complexity.LocalClauseEmitter
open TM2BooleanEncoding OutputLiteralEmitter

/-- Scalar form of the actual direct-network constraint. The cell position is
zero for control cells and its natural stack position for symbol cells. -/
theorem rawClause_eq_constraint (M : Turing.FinTM2) (f : Family M) (j r base nextBase : ℕ)
    (a : Fin (Fintype.card (Port M)) → Bool)
    (hpos : cellIndex M (familyCell M j r f) = j) :
    let H := j+r+1
    let N := directNetwork M H
    let v := cellEnumeration M H (familyCell M j r f)
    rawClause M f (fun p => a (portEnumeration M p)) j r base nextBase =
      TruthTableCNF.constraint (fun q => base+(N.ports v q).val) (nextBase+v.val) a (N.rule v a) := by
  dsimp only
  have hp : (ports M).map (fun p => (base+portAddress M (j+r+1) j p,!(a (portEnumeration M p)))) =
      List.ofFn (fun q : Fin (Fintype.card (Port M)) =>
        (base+((directNetwork M (j+r+1)).ports (cellEnumeration M (j+r+1) (familyCell M j r f)) q).val,!(a q))) := by
    simp only [ports,List.map_ofFn,Function.comp_def,Equiv.apply_symm_apply]
    apply congrArg List.ofFn
    funext q
    simp [directNetwork,encodedPorts,portAddress_correct,hpos]
  have hr : (directNetwork M (j+r+1)).rule (cellEnumeration M (j+r+1) (familyCell M j r f)) a =
      directRule M (j+r+1) (familyCell M j r f) (fun p => a (portEnumeration M p)) := by
    simp [directNetwork]
  simp only [rawClause,hp,TruthTableCNF.constraint,TruthTableCNF.mismatch,hr]

lemma variableEquiv_left_val (p n t : ℕ) (i : Fin p) :
    (InitialNetwork.variableEquiv p n t (Sum.inl i)).val = i.val := rfl

lemma variableEquiv_right_val (p n t : ℕ) (i : Fin (t+1)) (v : Fin n) :
    (InitialNetwork.variableEquiv p n t (Sum.inr (i,v))).val = p+i.val*n+v.val := by
  change p+(v.val+n*i.val) = _
  ring

/-- Mapping a local clause's explicit time/cell variables to the actual dense
CNF variable indices gives precisely the emitted scalar clause. -/
theorem rawClause_eq_dense_constraint (M : Turing.FinTM2) (f : Family M) (j r p T : ℕ)
    (i : Fin T) (a : Fin (Fintype.card (Port M)) → Bool)
    (hpos : cellIndex M (familyCell M j r f) = j) :
    let H := j+r+1
    let N := directNetwork M H
    let v := cellEnumeration M H (familyCell M j r f)
    let e := InitialNetwork.variableEquiv p (bitCount M H) T
    rawClause M f (fun q => a (portEnumeration M q)) j r
      (p+i.val*bitCount M H) (p+(i.val+1)*bitCount M H) =
      (TruthTableCNF.constraint (fun q => Sum.inr (i.castSucc,N.ports v q))
        (Sum.inr (i.succ,v)) a (N.rule v a)).map (fun l => ((e l.1).val,l.2)) := by
  dsimp only
  rw [rawClause_eq_constraint M f j r _ _ a hpos]
  simp only [TruthTableCNF.constraint,TruthTableCNF.mismatch,List.map_append,List.map_ofFn,
    List.map_cons,List.map_nil,Function.comp_def,variableEquiv_right_val,Fin.val_castSucc,Fin.val_succ]

end HiddenCircuits.Complexity.LocalClauseEmitter
