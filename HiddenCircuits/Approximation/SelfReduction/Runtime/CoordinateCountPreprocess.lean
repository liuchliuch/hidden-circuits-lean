import HiddenCircuits.Approximation.SamplerRuntime.CoordinateSampler
import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountingPadding

/-! New code transport: physically compile only the coordinate component of
an accuracy/confidence request, preserving both precisions and the fair tape. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.CoordinateCounting
open Complexity Complexity.OracleBlock GraphReduction Polynomial

def request (xs : BitString) : BitString := PairPreprocess.mapFirst GraphReduction.Runtime.CoordinateGraph.bits xs
def preprocess (xs : BitString) : BitString := PairPreprocess.mapFirst request xs
noncomputable def requestProgram : OracleBlock 35 := PairPreprocess.program GraphReduction.Runtime.CoordinateGraph.program
noncomputable def requestTime : Polynomial ℕ := PairPreprocess.time (k:=31)
  GraphReduction.Runtime.CoordinateGraph.time GraphReduction.Runtime.CoordinateGraph.size
noncomputable def requestSize : Polynomial ℕ := GraphVerifier.MatchingPullback.pairSize GraphReduction.Runtime.CoordinateGraph.size
noncomputable def preprocessProgram : OracleBlock 39 := PairPreprocess.program requestProgram
noncomputable def preprocessTime : Polynomial ℕ := PairPreprocess.time (k:=35) requestTime requestSize
noncomputable def preprocessSize : Polynomial ℕ := GraphVerifier.MatchingPullback.pairSize requestSize

lemma request_size (xs : BitString) : (request xs).length≤requestSize.eval xs.length :=
  GraphVerifier.MatchingPullback.pair_size GraphReduction.Runtime.CoordinateGraph.bits
    GraphReduction.Runtime.CoordinateGraph.size GraphReduction.Runtime.CoordinateGraph.size_bound xs
lemma preprocess_size (xs : BitString) : (preprocess xs).length≤preprocessSize.eval xs.length :=
  GraphVerifier.MatchingPullback.pair_size request requestSize request_size xs
lemma request_executes (g : BitString → ℕ) (xs : BitString) :
    ∃s c,requestProgram.Executes g (Function.update (fun _=>[]) 0 xs) s c ∧s 0=request xs ∧c≤requestTime.eval xs.length :=
  PairPreprocess.program_executes GraphReduction.Runtime.CoordinateGraph.program g GraphReduction.Runtime.CoordinateGraph.bits
    GraphReduction.Runtime.CoordinateGraph.time GraphReduction.Runtime.CoordinateGraph.size
    (GraphReduction.Runtime.CoordinateGraph.program_executes g) GraphReduction.Runtime.CoordinateGraph.size_bound xs
lemma preprocess_executes (g : BitString → ℕ) (xs : BitString) :
    ∃s c,preprocessProgram.Executes g (Function.update (fun _=>[]) 0 xs) s c ∧s 0=preprocess xs ∧c≤preprocessTime.eval xs.length :=
  PairPreprocess.program_executes requestProgram g request requestTime requestSize (request_executes g) request_size xs
lemma request_queryFree : requestProgram.QueryFree :=
  PairPreprocess.program_queryFree GraphReduction.Runtime.CoordinateGraph.program GraphReduction.Runtime.CoordinateGraph.program_queryFree
lemma preprocess_queryFree : preprocessProgram.QueryFree := PairPreprocess.program_queryFree requestProgram request_queryFree

@[simp] lemma request_canonical (xs : BitString) (r k : ℕ) :
    request (estimateInput xs r k)=estimateInput (GraphReduction.Runtime.CoordinateGraph.bits xs) r k := by
  simp [request,estimateInput,PairPreprocess.mapFirst]
@[simp] lemma preprocess_canonical (xs : BitString) (r k : ℕ) (tape : BitString) :
    preprocess (pairBits (estimateInput xs r k) tape)=
      pairBits (estimateInput (GraphReduction.Runtime.CoordinateGraph.bits xs) r k) tape := by
  simp [preprocess,PairPreprocess.mapFirst,request_canonical]
lemma preprocess_unpaired (xs : BitString) (h:unpairBits xs=none) : preprocess xs=[] := by
  simp [preprocess,PairPreprocess.mapFirst,h]
end HiddenCircuits.Approximation.SelfReduction.Runtime.CoordinateCounting
