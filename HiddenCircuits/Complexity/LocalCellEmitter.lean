import HiddenCircuits.Complexity.LocalClauseCorrectness

/-! Actual finite emission of every truth-table clause for one Boolean cell.
The pattern list is fixed by the verifier's local width, never by input length. -/
namespace HiddenCircuits.Complexity.LocalCellEmitter
open OracleBlock TM2BooleanEncoding OutputLiteralEmitter Polynomial

noncomputable def patterns (M : Turing.FinTM2) : List (Fin (Fintype.card (Port M)) → Bool) :=
  Finset.univ.toList

noncomputable def bits (M : Turing.FinTM2) (f : Family M) (j r base nextBase : ℕ) : BitString :=
  (patterns M).flatMap (fun a => serializedClause
    (LocalClauseEmitter.rawClause M f (fun p => a (portEnumeration M p)) j r base nextBase))

noncomputable def program (M : Turing.FinTM2) (f : Family M) : OracleBlock 7 :=
  sequence ((patterns M).map (fun a => LocalClauseEmitter.program M f (fun p => a (portEnumeration M p))))

noncomputable def time (M : Turing.FinTM2) (f : Family M) : Polynomial ℕ :=
  C (patterns M).length*LocalClauseEmitter.time M f+C (2*(patterns M).length+1)

/-- Exact real-program output for the whole constant-width local truth table. -/
theorem program_executes (g : BitString → ℕ) (M : Turing.FinTM2) (f : Family M)
    (j r base nextBase : ℕ) (stream : BitString) :
    ∃ cost, (program M f).Executes g (LocalClauseEmitter.state j base nextBase 0 0 0 r stream)
      (LocalClauseEmitter.state j base nextBase 0 0 0 r ((bits M f j r base nextBase).reverse++stream)) cost ∧
      cost ≤ (time M f).eval (j+r+base+nextBase) := by
  have hitem (a : Fin (Fintype.card (Port M)) → Bool) (_ : a ∈ patterns M) (acc : BitString) : ∃ cost,
      (LocalClauseEmitter.program M f (fun p => a (portEnumeration M p))).Executes g
        (Function.update (LocalClauseEmitter.state j base nextBase 0 0 0 r []) 6 acc)
        (Function.update (LocalClauseEmitter.state j base nextBase 0 0 0 r []) 6
          ((serializedClause (LocalClauseEmitter.rawClause M f (fun p => a (portEnumeration M p)) j r base nextBase)).reverse++acc)) cost ∧
      cost ≤ (LocalClauseEmitter.time M f).eval (j+r+base+nextBase) := by
    simpa only [LocalClauseEmitter.update_stream] using LocalClauseEmitter.program_executes g M f
      (fun p => a (portEnumeration M p)) j r base nextBase acc
  obtain ⟨cost,hc,hb⟩ := sequence_emit_bounded g (patterns M)
    (fun a => LocalClauseEmitter.program M f (fun p => a (portEnumeration M p)))
    (fun a => serializedClause (LocalClauseEmitter.rawClause M f (fun p => a (portEnumeration M p)) j r base nextBase))
    (fun _ => (LocalClauseEmitter.time M f).eval (j+r+base+nextBase))
    (LocalClauseEmitter.state j base nextBase 0 0 0 r []) 6 hitem stream
  refine ⟨cost,?_,?_⟩
  · simpa only [LocalClauseEmitter.update_stream] using hc
  · simpa [time,List.map_const] using hb

lemma program_queryFree (M : Turing.FinTM2) (f : Family M) : (program M f).QueryFree := by
  apply sequence_queryFree
  intro B hb
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp hb
  exact LocalClauseEmitter.program_queryFree _ _ _

/-- The serialized cell block is exactly the dense-index image of the actual
local clauses used by the count-preserving formula. -/
theorem bits_eq_localClauses (M : Turing.FinTM2) (f : Family M) (j r p T : ℕ) (i : Fin T)
    (hpos : cellIndex M (familyCell M j r f) = j) :
    let H := j+r+1
    let N := directNetwork M H
    let v := cellEnumeration M H (familyCell M j r f)
    let e := InitialNetwork.variableEquiv p (bitCount M H) T
    bits M f j r (p+i.val*bitCount M H) (p+(i.val+1)*bitCount M H) =
      (N.localClauses T i v).flatMap (fun c => serializedClause (c.map (fun l => ((e (Sum.inr l.1)).val,l.2)))) := by
  dsimp only
  simp only [bits,LocalNetwork.localClauses,TruthTableCNF.clauses,patterns,List.flatMap_assoc]
  apply List.flatMap_congr
  intro a ha
  simp only [List.ofFn_const,List.replicate_one,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  apply congrArg serializedClause
  rw [LocalClauseEmitter.rawClause_eq_dense_constraint M f j r p T i a hpos]
  simp only [TruthTableCNF.constraint,TruthTableCNF.mismatch,List.map_append,List.map_ofFn,
    List.map_cons,List.map_nil,Function.comp_def]

end HiddenCircuits.Complexity.LocalCellEmitter
