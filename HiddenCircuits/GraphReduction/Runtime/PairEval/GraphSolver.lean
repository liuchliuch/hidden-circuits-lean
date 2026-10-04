import HiddenCircuits.GraphReduction.Runtime.PairEval.DriverCell
import HiddenCircuits.GraphReduction.Runtime.PairEval.DriverInitialize
import HiddenCircuits.GraphReduction.Runtime.PairEval.DriverFinish
import HiddenCircuits.GraphReduction.Runtime.PairEval.GraphPromises

/-! Proposition 10.1 on arbitrary canonical PairEval instances. The finite
program parses its input, constructs its unary degree, executes one shared
probe loop, divides the final integer ratio exactly, and clears every workspace.
No algorithm or runtime certificate occurs in the endpoint theorem. -/
namespace HiddenCircuits.GraphReduction.Runtime.PairEval.GraphSolver
open Complexity OracleBlock BinaryArithmetic Polynomial
open Driver
set_option maxHeartbeats 1000000

noncomputable def finalInputP : Polynomial ℕ := 2*X+GraphBounds.degreeP+GraphBounds.accumulatorP+2
noncomputable def signedProgram (kind : Target) : OracleBlock 97 := seq setup (seq (probeLoop (cell kind)) finish)
noncomputable def signedTime (kind : Target) : Polynomial ℕ :=
  initializeTime+(GraphBounds.degreeP+1)*(cellTime kind+5)+1+finishTime.comp finalInputP+4
noncomputable def dropSign : OracleBlock 97 := branchPop 0 skip skip skip
noncomputable def program (kind : Target) : OracleBlock 97 := seq (signedProgram kind) dropSign
noncomputable def time (kind : Target) : Polynomial ℕ := signedTime kind+5

lemma final_state_bound (w : PairInput) (a : ℤ×ℤ)
    (ha : (signedBits a.1).length≤GraphBounds.accumulatorP.eval (pairInputBits w).length ∧
      (signedBits a.2).length≤GraphBounds.accumulatorP.eval (pairInputBits w).length) :
    ∀i,(state w 0 (degree w+1) a [] [] [] i).length≤finalInputP.eval (pairInputBits w).length := by
  have hp := (GraphBounds.parameter_bounds w).1
  have hh := (GraphBounds.parameter_bounds w).2.1
  have hd : degree w≤GraphBounds.degreeP.eval (pairInputBits w).length := (GraphBounds.parameter_bounds w).2.2
  intro i
  simp only [finalInputP,eval_add,eval_mul,eval_X,eval_ofNat]
  fin_cases i <;> norm_num only [state] <;>
    (try simp only [ite_true,ite_false,List.length_replicate,List.length_nil]) <;> omega

theorem signedProgram_executes (kind : Target) (g : BitString→ℕ) (w : PairInput) (hg : CorrectOracle kind g w) :
    ∃c,(signedProgram kind).Executes g (Function.update (fun _=>[]) 0 (pairInputBits w))
      (Function.update (fun _=>[]) 0 (signedBits (w.value:ℤ))) c ∧ c≤(signedTime kind).eval (pairInputBits w).length := by
  obtain ⟨a,ha,hab⟩ := initialize_executes g w
  obtain ⟨b,hb,hbb,hbits⟩ := probeLoop_executes (cell kind) (modelKind kind) g w _ _ (cell_spec kind g w hg)
    (GraphBounds.initialBitBound (modelKind kind) w)
  obtain ⟨c,hc,hcb⟩ := finish_executes g w 0 (degree w+1)
    (RationalAccumulator.run (0,1) (GraphRecovery.terms (modelKind kind) w)) (finalInputP.eval (pairInputBits w).length)
    (GraphRecovery.accumulator_nonzero _ _) (GraphRecovery.accumulator_divides _ _)
    (final_state_bound w _ hbits.head)
  rw [GraphRecovery.accumulator_quotient] at hc
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb hc),?_⟩
  have hd : degree w≤GraphBounds.degreeP.eval (pairInputBits w).length := (GraphBounds.parameter_bounds w).2.2
  have hm := Nat.mul_le_mul_right ((cellTime kind).eval (pairInputBits w).length+5) (Nat.add_le_add_right hd 1)
  simp only [signedTime,eval_add,eval_mul,eval_comp,eval_one,eval_ofNat]
  omega

lemma dropSign_executes (g : BitString→ℕ) (n : ℕ) :
    dropSign.Executes g (Function.update (fun _=>[]) 0 (signedBits (n:ℤ)))
      (Function.update (fun _=>[]) 0 (Computability.encodeNat n)) 3 := by
  apply branchPop_false (0:Fin 98) skip skip skip g
    (show (Function.update (fun _=>[]) 0 (signedBits (n:ℤ))) 0=false::Computability.encodeNat n by simp [signedBits,negative])
  simpa only [Function.update_idem] using skip_executes g (Function.update (fun _:Fin 98=>[]) 0 (Computability.encodeNat n))

theorem program_executes (kind : Target) (g : BitString→ℕ) (w : PairInput) (hg : CorrectOracle kind g w) :
    ∃c,(program kind).Executes g (Function.update (fun _=>[]) 0 (pairInputBits w))
      (Function.update (fun _=>[]) 0 (Computability.encodeNat (pairEval (pairInputBits w)))) c ∧
      c≤(time kind).eval (pairInputBits w).length := by
  obtain ⟨c,hc,hb⟩ := signedProgram_executes kind g w hg
  refine ⟨c+3+2,?_,?_⟩
  · simpa only [pairEval_pairInputBits] using seq_executes _ _ g hc (dropSign_executes g w.value)
  · simp only [time,eval_add,eval_ofNat];omega

/-- An encoded-domain reduction, whose domain includes every valid pair stream
and both arbitrary boundary masks. The malformed-zero extension is defined by
`pairEval`; this contract deliberately makes no malformed-input runtime claim. -/
def EncodedPairReduction (g : BitString→ℕ) : Prop :=
  ∃(B : OracleBlock 97) (P : Polynomial ℕ),∀w : PairInput,
    ∃c,B.Executes g (Function.update (fun _=>[]) 0 (pairInputBits w))
      (Function.update (fun _=>[]) 0 (Computability.encodeNat w.value)) c ∧ c≤P.eval (pairInputBits w).length

theorem encoded_reduction (kind : Target) (g : BitString→ℕ) (hg : ∀w,CorrectOracle kind g w) : EncodedPairReduction g := by
  refine ⟨program kind,time kind,?_⟩
  intro w
  simpa only [pairEval_pairInputBits] using program_executes kind g w (hg w)

lemma monotone_correct (g : BitString→ℕ) (hg : ClassMatchingOracle (fun G=>MonotoneGraph G.2.graph) g) :
    ∀w,CorrectOracle none g w := GraphPromises.monotone_spec g hg
lemma unit_correct (g : BitString→ℕ) (hg : ClassMatchingOracle (fun G=>UnitIntervalGraph G.2.graph) g) :
    ∀w,CorrectOracle (some .unit) g w := GraphPromises.unit_spec g hg
lemma private_correct (g : BitString→ℕ) (hg : ClassMatchingOracle (fun G=>ChordalPermutationGraph G.2.graph) g) :
    ∀w,CorrectOracle (some .privateGraph) g w := GraphPromises.private_spec g hg
lemma suppliedPrivate_correct (g : BitString→ℕ) (hg : SuppliedChordalPermutationOracle g) :
    ∀w,CorrectOracle (some .suppliedPrivate) g w := GraphPromises.suppliedPrivate_spec g hg

theorem pairEval_to_monotone (g : BitString→ℕ) (hg : ClassMatchingOracle (fun G=>MonotoneGraph G.2.graph) g) :
    EncodedPairReduction g := encoded_reduction none g (monotone_correct g hg)
theorem pairEval_to_unitInterval (g : BitString→ℕ) (hg : ClassMatchingOracle (fun G=>UnitIntervalGraph G.2.graph) g) :
    EncodedPairReduction g := encoded_reduction (some .unit) g (unit_correct g hg)
theorem pairEval_to_chordalPermutation (g : BitString→ℕ) (hg : ClassMatchingOracle (fun G=>ChordalPermutationGraph G.2.graph) g) :
    EncodedPairReduction g := encoded_reduction (some .privateGraph) g (private_correct g hg)
theorem pairEval_to_suppliedChordalPermutation (g : BitString→ℕ) (hg : SuppliedChordalPermutationOracle g) :
    EncodedPairReduction g := encoded_reduction (some .suppliedPrivate) g (suppliedPrivate_correct g hg)

/-- Concrete total natural graph-counting oracles discharge every promise. -/
theorem canonical_graph_program (kind : Target) (hk : kind≠some .suppliedPrivate) (w : PairInput) :
    ∃c,(program kind).Executes GraphInput.perfectMatchingProblem (Function.update (fun _=>[]) 0 (pairInputBits w))
      (Function.update (fun _=>[]) 0 (Computability.encodeNat w.value)) c ∧ c≤(time kind).eval (pairInputBits w).length := by
  simpa only [pairEval_pairInputBits] using program_executes kind GraphInput.perfectMatchingProblem w (by
    intro s
    cases kind with
    | none => exact GraphPromises.canonical_spec none w s
    | some k => cases k with
      | unit => exact GraphPromises.canonical_spec (some false) w s
      | privateGraph => exact GraphPromises.canonical_spec (some true) w s
      | suppliedPrivate => exact (hk rfl).elim)
theorem canonical_supplied_program (w : PairInput) :
    ∃c,(program (some .suppliedPrivate)).Executes GraphPromises.suppliedPrivateProblem
      (Function.update (fun _=>[]) 0 (pairInputBits w))
      (Function.update (fun _=>[]) 0 (Computability.encodeNat w.value)) c ∧
      c≤(time (some .suppliedPrivate)).eval (pairInputBits w).length := by
  simpa only [pairEval_pairInputBits] using program_executes (some .suppliedPrivate) GraphPromises.suppliedPrivateProblem w
    (GraphPromises.suppliedPrivate_canonical w)
end HiddenCircuits.GraphReduction.Runtime.PairEval.GraphSolver
