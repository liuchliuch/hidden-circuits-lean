import HiddenCircuits.Complexity.TimeEmitter
import HiddenCircuits.Complexity.CellEnumeration

/-! Exact stream ordering for the actual row emitter, linked to the concrete
row-major local-network constraints rather than only to its scalar templates. -/
namespace HiddenCircuits.Complexity.RowEmitter
open TM2BooleanEncoding OutputLiteralEmitter

/-- Closed finite-list form of the physically scanned stack-position loop. -/
theorem stackBits_ofFn (M : Turing.FinTM2) (base nextBase j r : ℕ) :
    stackBits M base nextBase j r =
      (List.ofFn (fun i : Fin r => FamilyEmitter.bits M (FamilyEmitter.symbols M)
        (j+i.val) (r-1-i.val) base nextBase)).flatten := by
  induction r generalizing j with
  | zero => simp [stackBits]
  | succ r ih =>
    rw [stackBits,List.ofFn_succ,List.flatten_cons,ih]
    simp only [Fin.val_zero,Fin.val_succ,Nat.add_zero,Nat.add_sub_cancel,Nat.sub_zero]
    apply congrArg₂ List.append rfl
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext i
    congr 1 <;> omega

noncomputable def indexedCellBits (M : Turing.FinTM2) (H p T : ℕ) (i : Fin T) (c : Cell M H) : BitString :=
  ((directNetwork M H).localClauses T i (cellEnumeration M H c)).flatMap
    (fun cl => serializedClause (cl.map (fun l =>
      ((InitialNetwork.variableEquiv p (bitCount M H) T (Sum.inr l.1)).val,l.2))))

/-- Control-cell stream identity, with the verifier's positive height made explicit. -/
lemma control_cell_bits (M : Turing.FinTM2) (H p T : ℕ) (hH : 0<H) (i : Fin T) (q : Control M) :
    LocalCellEmitter.bits M (Sum.inl q) 0 (H-1)
      (p+i.val*bitCount M H) (p+(i.val+1)*bitCount M H) = indexedCellBits M H p T i (Sum.inl q) := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : H≠0)
  have h := LocalCellEmitter.bits_eq_localClauses M (Sum.inl q) 0 r p T i rfl
  simp only [familyCell] at h
  rw [show 0+r+1=r+1 by omega] at h
  simpa [indexedCellBits] using h

/-- Stack-cell stream identity for the real dense variable numbering. -/
lemma stack_cell_bits (M : Turing.FinTM2) (H p T : ℕ) (i : Fin T) (k : M.K)
    (j : Fin H) (symbol : Option (Symbol M k)) :
    LocalCellEmitter.bits M (Sum.inr ⟨k,symbol⟩) j.val (H-1-j.val)
      (p+i.val*bitCount M H) (p+(i.val+1)*bitCount M H) =
      indexedCellBits M H p T i (Sum.inr ⟨k,(j,symbol)⟩) := by
  rcases j with ⟨j,hj⟩
  obtain ⟨r,he⟩ : ∃ r, H=j+r+1 := ⟨H-j-1,by omega⟩
  subst H
  have h := LocalCellEmitter.bits_eq_localClauses M (Sum.inr ⟨k,symbol⟩) j r p T i rfl
  simpa [indexedCellBits,familyCell,show j+r+1-1-j=r by omega] using h

/-- The entire real row stream has the exact encoded row-major cell order. -/
theorem bits_eq_row (M : Turing.FinTM2) (H p T : ℕ) (hH : 0<H) (i : Fin T) :
    bits M H (p+i.val*bitCount M H) (p+(i.val+1)*bitCount M H) =
      (List.ofFn (fun v : Fin (bitCount M H) =>
        indexedCellBits M H p T i ((cellEnumeration M H).symm v))).flatten := by
  rw [ofFn_cells,List.flatten_append]
  unfold bits
  apply congrArg₂ List.append
  · simp only [FamilyEmitter.bits,FamilyEmitter.controls,List.flatMap_def,List.map_ofFn,Function.comp_def]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext q
    exact control_cell_bits M H p T hH i ((Fintype.equivFin (Control M)).symm q)
  · rw [stackBits_ofFn,List.flatten_flatten,List.map_ofFn]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext j
    simp only [Function.comp_def,FamilyEmitter.bits,FamilyEmitter.symbols,List.flatMap_def,List.map_ofFn,Function.comp_def,Nat.zero_add]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext s
    simpa only [Sigma.eta] using stack_cell_bits M H p T i ((symbolEnumeration M).symm s).1 j ((symbolEnumeration M).symm s).2

end HiddenCircuits.Complexity.RowEmitter
