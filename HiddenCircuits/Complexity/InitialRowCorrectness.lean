import HiddenCircuits.Complexity.InitialRowSemantics
import HiddenCircuits.Complexity.InitialRowRuntime
import HiddenCircuits.Complexity.UniformSerialization

/-! Exact equality between the uniform operational initial-row output and the
actual encoded source clauses, in the original dense variable order. -/
namespace HiddenCircuits.Complexity.InitialRowEmitter
open TM2BooleanEncoding InitialSourceClassifier
variable {v : BitString → Bool}
variable (M : Turing.TM2ComputableInPolyTime id Computability.encodeBool v)

noncomputable def initialSources (x : BitString) (m H : ℕ) : Fin (bitCount M.tm H) → InputSource m :=
  fun i => VerifierTableau.cellSource M H (certificateSources x m) ((cellEnumeration M.tm H).symm i)

lemma initialStream_eq_cells (x : BitString) (m H T : ℕ) :
    InitialNetwork.initialStream T (initialSources M x m H) =
      (List.ofFn (fun i : Fin (bitCount M.tm H) =>
        InitialCellEmitter.bits (m+i.val) (initialSources M x m H i))).flatten := by
  unfold InitialNetwork.initialStream InitialNetwork.inputClauses
  simp only [List.flatMap_def,List.map_flatten,List.flatten_flatten,List.map_map,List.map_ofFn,Function.comp_def]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  simpa only [List.flatMap_def] using (InitialCellEmitter.bits_eq_sourceClauses T i (initialSources M x m H i)).symm

/-- Every emitted byte agrees with the true initial tableau constraints,
including input escaping, witness signs, empty padding, and dense index order. -/
theorem bits_eq_initialStream (x : BitString) (m H T : ℕ) (hH : 2*x.length+m+1≤H) :
    bits M x m H = InitialNetwork.initialStream T (initialSources M x m H) := by
  rw [bits_eq_scan M x m H hH,initialStream_eq_cells]
  let F : Cell M.tm H → BitString := fun cell =>
    InitialCellEmitter.bits (m+(cellEnumeration M.tm H cell).val)
      (VerifierTableau.cellSource M H (certificateSources x m) cell)
  have he : (List.ofFn (fun i : Fin (bitCount M.tm H) =>
      InitialCellEmitter.bits (m+i.val) (initialSources M x m H i))).flatten =
      (List.ofFn (fun i : Fin (bitCount M.tm H) => F ((cellEnumeration M.tm H).symm i))).flatten := by
    simp only [F,Equiv.apply_symm_apply,initialSources]
  rw [he,ofFn_cells,List.flatten_append]
  apply congrArg₂ List.append
  · rw [InitialRowFamily.controlBits,InitialRowFamily.controls,InitialRowFamily.walkBits_ofFn]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext q
    simp [F,cellEnumeration_control_val,cellSource_control,InitialCellEmitter.bits]
  · rw [scanBits_ofFn,List.flatten_flatten,List.map_ofFn]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext j
    rw [slotBits,InitialRowFamily.symbols,InitialRowFamily.walkBits_ofFn]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext a
    simp only [F,Function.comp_def,cellEnumeration_stack_val,Sigma.eta,Equiv.apply_symm_apply]
    rw [cellSource_symbol]
    have ht : m+controlBits M.tm+j.val*symbolBits M.tm+a.val =
        m+(controlBits M.tm+j.val*symbolBits M.tm+a.val) := by omega
    rw [ht]
    cases hs : (certificateSources x m)[j.val]? <;> rfl

lemma initialSources_eq (x : BitString) (m : ℕ) :
    initialSources M x m (VerifierTableau.height M x m) = VerifierTableau.sources M x m := rfl

/-- Direct clean operational endpoint for the genuine compiler's initial stream. -/
theorem initialStream_executes (g : BitString → ℕ) (x : BitString) (m H T : ℕ)
    (hH : 2*x.length+m+1≤H) (stream : BitString) :
    ∃ cost, (cleanProgram M).Executes g (state 0 0 x m H [] 0 0 stream)
      (state 0 0 x m H [] 0 0
        ((InitialNetwork.initialStream T (initialSources M x m H)).reverse++stream)) cost ∧
      cost ≤ (cleanTime M).eval (x.length+m+H) := by
  rw [←bits_eq_initialStream M x m H T hH]
  exact cleanProgram_executes M g x m H hH stream

/-- At the compiler's actual height, the sizing precondition is discharged by
its proved construction; callers need no separate bound or runtime certificate. -/
theorem verifierInitialStream_executes (g : BitString → ℕ) (x : BitString) (m : ℕ) (stream : BitString) :
    ∃ cost, (cleanProgram M).Executes g
      (state 0 0 x m (VerifierTableau.height M x m) [] 0 0 stream)
      (state 0 0 x m (VerifierTableau.height M x m) [] 0 0
        ((InitialNetwork.initialStream (VerifierTableau.horizon M x m) (VerifierTableau.sources M x m)).reverse++stream)) cost ∧
      cost ≤ (cleanTime M).eval (x.length+m+VerifierTableau.height M x m) := by
  exact initialStream_executes M g x m (VerifierTableau.height M x m) (VerifierTableau.horizon M x m)
    (by unfold VerifierTableau.height;omega) stream

end HiddenCircuits.Complexity.InitialRowEmitter
