import HiddenCircuits.GraphReduction.Runtime.UnitCoordinateMembership
import HiddenCircuits.Approximation.SamplerRuntime.GraphPaddingSampler

/-! Physical preprocessing of the coordinate component of a sampling request,
then of the request component of the outer random-tape pair. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.CoordinateSampler
open Complexity Complexity.OracleBlock GraphReduction Polynomial

/-- The input representation, not a supplied adjacency matrix, is compiled. -/
def request (xs : BitString) : BitString := PairPreprocess.mapFirst Runtime.CoordinateGraph.bits xs
def preprocess (xs : BitString) : BitString := PairPreprocess.mapFirst request xs
noncomputable def requestProgram : OracleBlock 35 := PairPreprocess.program Runtime.CoordinateGraph.program
noncomputable def requestTime : Polynomial ℕ := PairPreprocess.time (k:=31) Runtime.CoordinateGraph.time Runtime.CoordinateGraph.size
noncomputable def requestSize : Polynomial ℕ := GraphVerifier.MatchingPullback.pairSize Runtime.CoordinateGraph.size
noncomputable def preprocessProgram : OracleBlock 39 := PairPreprocess.program requestProgram
noncomputable def preprocessTime : Polynomial ℕ := PairPreprocess.time (k:=35) requestTime requestSize
noncomputable def preprocessSize : Polynomial ℕ := GraphVerifier.MatchingPullback.pairSize requestSize

lemma request_size (xs : BitString) : (request xs).length≤requestSize.eval xs.length :=
  GraphVerifier.MatchingPullback.pair_size Runtime.CoordinateGraph.bits Runtime.CoordinateGraph.size Runtime.CoordinateGraph.size_bound xs
lemma preprocess_size (xs : BitString) : (preprocess xs).length≤preprocessSize.eval xs.length :=
  GraphVerifier.MatchingPullback.pair_size request requestSize request_size xs

lemma request_executes (g : BitString → ℕ) (xs : BitString) :
    ∃s c,requestProgram.Executes g (Function.update (fun _=>[]) 0 xs) s c ∧
      s 0=request xs ∧c≤requestTime.eval xs.length :=
  PairPreprocess.program_executes Runtime.CoordinateGraph.program g Runtime.CoordinateGraph.bits Runtime.CoordinateGraph.time Runtime.CoordinateGraph.size
    (Runtime.CoordinateGraph.program_executes g) Runtime.CoordinateGraph.size_bound xs

lemma preprocess_executes (g : BitString → ℕ) (xs : BitString) :
    ∃s c,preprocessProgram.Executes g (Function.update (fun _=>[]) 0 xs) s c ∧
      s 0=preprocess xs ∧c≤preprocessTime.eval xs.length :=
  PairPreprocess.program_executes requestProgram g request requestTime requestSize
    (request_executes g) request_size xs

lemma request_queryFree : requestProgram.QueryFree :=
  PairPreprocess.program_queryFree Runtime.CoordinateGraph.program Runtime.CoordinateGraph.program_queryFree
lemma preprocess_queryFree : preprocessProgram.QueryFree :=
  PairPreprocess.program_queryFree requestProgram request_queryFree

@[simp] lemma request_canonical (xs : BitString) (k : ℕ) :
    request (sampleInput xs k)=sampleInput (Runtime.CoordinateGraph.bits xs) k := by
  simp [request,sampleInput,PairPreprocess.mapFirst]
@[simp] lemma preprocess_canonical (xs : BitString) (k : ℕ) (tape : BitString) :
    preprocess (pairBits (sampleInput xs k) tape)=pairBits (sampleInput (Runtime.CoordinateGraph.bits xs) k) tape := by
  simp [preprocess,PairPreprocess.mapFirst,request_canonical]

/-- Total malformed-input extension: malformed outer pairings map to empty;
otherwise both paired components are parsed and graph compilation is permissive. -/
lemma preprocess_unpaired (xs : BitString) (h : unpairBits xs=none) : preprocess xs=[] := by
  simp [preprocess,PairPreprocess.mapFirst,h]

end HiddenCircuits.Approximation.SamplerRuntime.CoordinateSampler
