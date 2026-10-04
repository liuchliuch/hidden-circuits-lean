import HiddenCircuits.Complexity.TimeCorrectness
import HiddenCircuits.Complexity.UniformVerifier

/-! Exact decomposition of the full verifier-CNF binary encoding into header,
initial constraints, transition stream, and the final accepting unit clause. -/
namespace HiddenCircuits.Complexity
open BoolCircuit TM2BooleanEncoding

theorem reindexCNF_bits {V : Type*} {n : ℕ} (e : V ≃ Fin n) (cs : RawCNF V) :
    (reindexCNF e cs).bits = List.replicate (2*n) true ++ false ::
      cs.flatMap (fun c => serializedClause (c.map (fun l => ((e l.1).val,l.2)))) := by
  rw [CNF.bits_eq_serialized]
  simp [reindexCNF,finiteCNF,serializedCNF,List.ofFn_get,List.map_map,List.flatMap_map,Function.comp_def]

namespace InitialNetwork
variable {p n r : ℕ}

noncomputable def initialStream (T : ℕ) (sources : Fin n → InputSource p) : BitString :=
  (inputClauses T sources).flatMap (fun c => serializedClause
    (c.map (fun l => ((variableEquiv p n T l.1).val,l.2))))

noncomputable def transitionStream (N : LocalNetwork n r) (T : ℕ) : BitString :=
  (N.orderedClauses T).flatMap (fun c => serializedClause
    (c.map (fun l => ((variableEquiv p n T (Sum.inr l.1)).val,l.2))))

/-- The decoder sees exactly the intended finite input, not an alternate or
implicit representation of the formula. -/
theorem orderedCNF_bits_decomposition (N : LocalNetwork n r) (T : ℕ)
    (sources : Fin n → InputSource p) (out : Fin n) :
    (orderedCNF N T sources out).bits =
      List.replicate (2*(p+(T+1)*n)) true ++ false ::
        (initialStream T sources ++ transitionStream (p := p) N T ++
          serializedClause [(p+T*n+out.val,true)]) := by
  rw [orderedCNF,reindexCNF_bits]
  simp [orderedClauses,LocalNetwork.orderedAcceptingClauses,initialStream,transitionStream,
    List.flatMap_append,List.flatMap_map,List.map_map,Function.comp_def,
    LocalClauseEmitter.variableEquiv_right_val,List.append_assoc]
end InitialNetwork

namespace VerifierTableau
variable {v : BitString → Bool}
variable (M : Turing.TM2ComputableInPolyTime id Computability.encodeBool v)

/-- The accepting output cell lies at position zero of the output stack, so its
in-row index is a fixed verifier constant independent of input height. -/
noncomputable def outputOffset (ht : HasTrueSymbol M) : ℕ :=
  controlBits M.tm+symbolIndex M.tm M.tm.k₁ (some ⟨M.outputAlphabet.invFun true,ht⟩)

lemma outputWire_val (x : BitString) (m : ℕ) (ht : HasTrueSymbol M) :
    (outputWire M x m ht).val = outputOffset M ht := by
  simp [outputWire,outputCell,cellEnumeration_stack_val,outputOffset,symbolIndex]

/-- Whole-stream equality for the source emitter's four stages. -/
theorem uniformPositiveFormula_stream (x : BitString) (m : ℕ) (ht : HasTrueSymbol M) :
    (uniformPositiveFormula M x m ht).bits =
      List.replicate (2*(m+(horizon M x m+1)*bitCount M.tm (height M x m))) true ++ false ::
      (InitialNetwork.initialStream (horizon M x m) (sources M x m) ++
        TimeEmitter.bits M.tm (height M x m) (bitCount M.tm (height M x m))
          m (m+bitCount M.tm (height M x m)) (horizon M x m) ++
        serializedClause [(m+horizon M x m*bitCount M.tm (height M x m)+outputOffset M ht,true)]) := by
  rw [uniformPositiveFormula,InitialNetwork.orderedCNF_bits_decomposition,outputWire_val]
  congr 3
  rw [TimeEmitter.bits_eq_orderedClauses M.tm _ _ _ (height_positive M x m)]
  rfl

end VerifierTableau
end HiddenCircuits.Complexity
