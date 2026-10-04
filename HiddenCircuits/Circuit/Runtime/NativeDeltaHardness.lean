import HiddenCircuits.Circuit.Runtime.NativeConstraintCallSource
import HiddenCircuits.Circuit.Runtime.SpectralConstraintDriver

/-! Closed #P hardness of the independently encoded native Delta evaluation
problem. The finite canonical #IS program constructs the N/CZ circuit, calls
its concrete spectral Delta solver in a disjoint bank, and exact-divides the
source dyadic scalar. The #P foundation substitutes this actual program into
its checked #SAT-to-#IS machine; no reduction-transitivity axiom is used. -/
namespace HiddenCircuits.Circuit.Runtime.NativeDeltaHardness
open Complexity OracleBlock Polynomial

noncomputable def program : OracleBlock 103 :=
  NativeConstraintSource.program SpectralConstraintEvaluation.program
noncomputable def time : Polynomial ℕ :=
  NativeConstraintSource.time SpectralConstraintEvaluation.time

lemma solverSpec (g : BitString→ℕ) (hg : DeltaOracle g) :
    NativeConstraintCall.SolverSpec SpectralConstraintEvaluation.program g SpectralConstraintEvaluation.time := by
  intro C
  simpa only [RationalOracleEncoding.encode_code] using SpectralConstraintEvaluation.native_executes g hg C

theorem program_executes (g : BitString→ℕ) (hg : DeltaOracle g) (G : GraphInput) :
    ∃c,program.Executes g (Function.update (fun _ : Fin 104=>[]) 0 G.encode)
      (Function.update (fun _ : Fin 104=>[]) 0 (Computability.encodeNat G.2.independentCount)) c ∧
      c ≤ time.eval G.encode.length :=
  NativeConstraintSource.program_executes _ g _ (solverSpec g hg) G

theorem sharpPHard_of_oracle (g : BitString→ℕ) (hg : DeltaOracle g) : SharpPHard g := by
  apply sharpPHard_of_canonical_independent_block g program time
  intro G
  obtain ⟨c,hc,hb⟩:=program_executes g hg G
  exact ⟨_,c,hc,Function.update_self _ _ _,hb⟩

/-- Unconditional hardness of the total, native rational-coded Delta problem. -/
theorem deltaEval_sharpPHard : SharpPHard deltaProblem :=
  sharpPHard_of_oracle deltaProblem deltaProblem_oracle

/-- All-raw #IS reduction obtained from the checked machine-grounded #P source
foundation, including noncanonical and malformed graph encodings. -/
theorem independentSet_to_deltaOracle (g : BitString→ℕ) (hg : DeltaOracle g) :
    PolyTuringReduction GraphInput.independentSetProblem g :=
  sharpPHard_of_oracle g hg _ GraphVerifier.Runtime.independentSet_sharpP

theorem independentSet_to_deltaEval : PolyTuringReduction GraphInput.independentSetProblem deltaProblem :=
  independentSet_to_deltaOracle deltaProblem deltaProblem_oracle
end HiddenCircuits.Circuit.Runtime.NativeDeltaHardness
