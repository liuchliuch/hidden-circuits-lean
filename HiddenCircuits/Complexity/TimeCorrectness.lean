import HiddenCircuits.Complexity.RowCorrectness

/-! Exact equality between the nested operational emitter's stream and the
row-major transition CNF in the count-preserving verifier construction. -/
namespace HiddenCircuits.Complexity.TimeEmitter
open TM2BooleanEncoding

lemma flatMap_flatten {α β : Type*} (xs : List (List α)) (f : α → List β) :
    xs.flatten.flatMap f = (xs.map (fun x => x.flatMap f)).flatten := by
  induction xs <;> simp [List.flatMap_append, *]

theorem bits_ofFn (M : Turing.FinTM2) (H cells base nextBase t : ℕ) :
    bits M H cells base nextBase t =
      (List.ofFn (fun i : Fin t => RowEmitter.bits M H
        (base+i.val*cells) (nextBase+i.val*cells))).flatten := by
  induction t generalizing base nextBase with
  | zero => simp [bits]
  | succ t ih =>
    rw [bits,List.ofFn_succ,List.flatten_cons,ih]
    simp only [Fin.val_zero,Fin.val_succ,Nat.zero_mul,Nat.add_zero]
    apply congrArg₂ List.append rfl
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext i
    congr 1 <;> ring

/-- The full actual transition stream is exactly the dense-index serialization
of the formula's ordered clauses, including all local truth-table multiplicities. -/
theorem bits_eq_orderedClauses (M : Turing.FinTM2) (H p T : ℕ) (hH : 0<H) :
    bits M H (bitCount M H) p (p+bitCount M H) T =
      ((directNetwork M H).orderedClauses T).flatMap (fun c => serializedClause
        (c.map (fun l => ((InitialNetwork.variableEquiv p (bitCount M H) T (Sum.inr l.1)).val,l.2)))) := by
  rw [bits_ofFn]
  simp only [LocalNetwork.orderedClauses,flatMap_flatten,List.map_ofFn,Function.comp_def]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  rw [show p+bitCount M H+i.val*bitCount M H=p+(i.val+1)*bitCount M H by ring]
  rw [RowEmitter.bits_eq_row M H p T hH i]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext v
  simp only [RowEmitter.indexedCellBits,Equiv.apply_symm_apply]

end HiddenCircuits.Complexity.TimeEmitter
