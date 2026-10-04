import HiddenCircuits.ExactSampling.Runtime.MainProgram
import HiddenCircuits.ExactSampling.PrefixCodes

/-!
# Exact uniform perfect matchings in expected polynomial random-bit time

This endpoint uses a finite fair-coin program with genuine binary-stack code at
every deterministic leaf. A complete trace is the exact list of rejected bit
blocks followed by its first accepted block; every such trace is realized by
the closed program. Their fair-bit masses sum to one, and the complete charged
work has a polynomial expectation in the original graph encoding length.
-/
namespace HiddenCircuits.ExactSampling
open Complexity DH Approximation Approximation.FiniteChains DHWeights
open Runtime Rejection
open scoped BigOperators

/-- Count-free decoding of the emitted local-vertex matching representation. -/
noncomputable def decodeMatching {n : ℕ} (G : MatrixGraph n) (bits : BitString) :
    Option (PerfectMatching G.graph) := do
  let path ← decodeSample bits
  let words ← decodeBitList path
  let p ← DHPaths.decode (words.map List.length) n G
  pure p.toMatching

 theorem decode_sampledWord {n : ℕ} (G : MatrixGraph n) (hG : DistanceHereditaryGraph G.graph)
    (x : Fin (count ⟨n,G⟩)) :
    decodeMatching G (Main.sampledWord G hG x)=some (DHIndex.unrank G hG x) := by
  simp [decodeMatching,Main.sampledWord,decodeSample,DHPaths.encode,decodeBitList_encode,
    List.map_map,Function.comp_def,DHPaths.choices_decode,DHIndex.unrank]

/-- Actual output-fiber probabilities of the finite experiments realized by the
closed program, rather than an independently stipulated uniform distribution. -/
noncomputable def outputMass {n : ℕ} (G : MatrixGraph n) (hG : DistanceHereditaryGraph G.graph)
    (M : PerfectMatching G.graph) (t : ℕ) : ℝ := by
  classical
  exact (Fintype.card {r : DHIndex.Experiment G t //
    decodeMatching G (Main.sampledWord G hG r.2)=some M} : ℝ) /
    (2^((t+1)*width (count ⟨n,G⟩)) : ℝ)

 theorem outputMass_eq {n : ℕ} (G : MatrixGraph n) (hG : DistanceHereditaryGraph G.graph)
    (M : PerfectMatching G.graph) (t : ℕ) : outputMass G hG M t=DHIndex.matchingMass G hG M t := by
  classical
  unfold outputMass DHIndex.matchingMass
  simp only [decode_sampledWord,Option.some.injEq,DHIndex.experimentOutput]

 theorem exact_uniform {n : ℕ} (G : MatrixGraph n) (hG : DistanceHereditaryGraph G.graph)
    (M : PerfectMatching G.graph) :
    ∑'t,outputMass G hG M t=1/(perfectMatchingCount G.graph : ℝ) := by
  simp_rw [outputMass_eq]
  exact DHIndex.exact_uniform G hG M

/-- Exact fair-bit weight of all terminating experiments at one retry count. -/
noncomputable def terminatingMass (G : GraphInput) (t : ℕ) : ℝ :=
  (count G : ℝ)*outcomeMass (count G) t

 theorem almost_sure_termination (G : GraphInput) (hc : 0<count G) :
    ∑'t,terminatingMass G t=1 := terminates_almost_surely hc

/-- Uniform upper bound on actual executions with the indicated retry count.
The variable term charges every full trial, not just the eventual successful one. -/
noncomputable def workEnvelope (G : GraphInput) (t : ℕ) : ℕ :=
  Main.fixedTime.eval G.encode.length+(t+1)*120*(Nat.size (count G)+1)

 theorem realized_trace (G : GraphInput) (hG : DistanceHereditaryGraph G.2.graph) (hc : 0<count G)
    (t : ℕ) (r : Trace (count G) t) (x : Fin (count G)) :
    ∃c,FairCode.Runs Main.program (Main.input G.encode)
      (Main.output (Main.sampledWord G.2 hG x)) (FairDraw.fairReads hc t r x) c ∧
      c≤workEnvelope G t ∧
      decodeMatching G.2 (Main.sampledWord G.2 hG x)=some (DHIndex.unrank G.2 hG x) := by
  obtain ⟨c,hc',hb⟩ := Main.positive_runs G.2 hG hc t r x
  exact ⟨c,hc',hb,decode_sampledWord G.2 hG x⟩

noncomputable def expectedWorkEnvelope (G : GraphInput) : ℝ :=
  ∑'t,terminatingMass G t*(workEnvelope G t : ℝ)

 theorem expectedWorkEnvelope_eq (G : GraphInput) (hc : 0<count G) :
    expectedWorkEnvelope G=((Main.fixedTime.eval G.encode.length : ℕ) : ℝ)+
      120*(Nat.size (count G)+1)*expectedAttempts (count G) := by
  have hmass := (outcomeMass_hasSum hc).mul_left (count G : ℝ)
  have hn : (count G : ℝ)≠0 := by exact_mod_cast hc.ne'
  have hmass' : HasSum (terminatingMass G) (1:ℝ) := by simpa [terminatingMass,hn] using hmass
  have htime := (weighted_attempts_hasSum hc).mul_left (120*((Nat.size (count G) : ℝ)+1))
  have h := (hmass'.mul_right ((Main.fixedTime.eval G.encode.length : ℕ) : ℝ)).add htime
  convert h.tsum_eq using 1
  · unfold expectedWorkEnvelope
    congr 1
    funext t
    unfold terminatingMass workEnvelope
    push_cast
    ring
  · ring

open Polynomial in
noncomputable def expectedTimePolynomial : Polynomial ℕ :=
  Main.fixedTime+240*(X+DH.BinaryRuntime.time+1)+2*X+10

 theorem expected_polynomial_work (G : GraphInput) (hG : DistanceHereditaryGraph G.2.graph)
    (hc : 0<count G) : expectedWorkEnvelope G≤((expectedTimePolynomial.eval G.encode.length : ℕ) : ℝ) := by
  rw [expectedWorkEnvelope_eq G hc]
  have hsize := count_word_length G hG
  rw [encodeNat_length] at hsize
  have hs : (Nat.size (count G) : ℝ)≤G.encode.length+DH.BinaryRuntime.time.eval G.encode.length := by exact_mod_cast hsize
  have htwo := expectedAttempts_lt_two hc
  have hb : 120*((Nat.size (count G) : ℝ)+1)*expectedAttempts (count G)≤
      240*((Nat.size (count G) : ℝ)+1) := by nlinarith
  simp only [expectedTimePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,
    Polynomial.eval_ofNat,Polynomial.eval_one]
  push_cast
  linarith

 theorem expected_polynomial_random_bits (G : GraphInput) (hG : DistanceHereditaryGraph G.2.graph)
    (hc : 0<count G) : expectedBits (count G)≤2*(G.encode.length+DH.BinaryRuntime.time.eval G.encode.length) := by
  have hs := count_word_length G hG
  rw [encodeNat_length] at hs
  have hr : (Nat.size (count G) : ℝ)≤G.encode.length+DH.BinaryRuntime.time.eval G.encode.length := by exact_mod_cast hs
  exact (expectedBits_le hc).trans (by linarith)

 theorem zero_count_failure (G : GraphInput) (hG : DistanceHereditaryGraph G.2.graph)
    (hz : perfectMatchingCount G.2.graph=0) :
    ∃c,FairCode.Runs Main.program (Main.input G.encode) (Main.output []) [] c ∧
      c≤CountWidth.timePolynomial.eval G.encode.length+G.encode.length+5 := by
  apply Main.zero_runs
  change count G=0
  exact (count_correct G hG).trans hz

 theorem empty_graph_success (G : MatrixGraph 0) (hG : DistanceHereditaryGraph G.graph) :
    ∃c,FairCode.Runs Main.program (Main.input (GraphInput.encode ⟨0,G⟩)) (Main.output [true]) [] c ∧
      decodeMatching G [true]=some (DHIndex.emptyPartner G).toMatching := by
  have hc := DHIndex.empty_count G hG
  let x : Fin (count ⟨0,G⟩) := ⟨0,by omega⟩
  obtain ⟨c,hr,hb⟩ := Main.positive_runs G hG (by omega) 0 Fin.elim0 x
  refine ⟨c,?_,?_⟩
  · simpa [Main.sampledWord,DHPaths.choices,DHPaths.encode,encodeBitList,FairDraw.fairReads,hc,
      width,acceptedTape] using hr
  · simp [decodeMatching,decodeSample,decodeBitList,DHPaths.decode,decodeBitListFuel]

 theorem quasiChains_exact_uniform {n : ℕ} (G : MatrixGraph n) (hG : QuasiChains G.graph)
    (M : PerfectMatching G.graph) :
    ∑'t,outputMass G (quasiChains_distanceHereditary hG) M t=1/(perfectMatchingCount G.graph : ℝ) :=
  exact_uniform G _ M

 theorem quasiChains_expected_polynomial_work (G : GraphInput) (hG : QuasiChains G.2.graph)
    (hc : 0<count G) : expectedWorkEnvelope G≤((expectedTimePolynomial.eval G.encode.length : ℕ) : ℝ) :=
  expected_polynomial_work G (quasiChains_distanceHereditary hG) hc

/-- Each branch/residual-rank pair occupies exactly one parent rank. This
is the joint law behind the adaptive proportional-count deletion algorithm. -/
 theorem adaptive_joint_probability {N : ℕ} (G : MatrixGraph (N+1))
    (hG : DistanceHereditaryGraph G.graph) (j : Fin (N+1)) (k : Fin (weight G j)) :
    SelfReduction.probability (fun x : Fin (count ⟨N+1,G⟩) => splitIndex G hG x=⟨j,k⟩)=
      1/(count ⟨N+1,G⟩ : ℚ) := by
  classical
  have he (x : Fin (count ⟨N+1,G⟩)) : splitIndex G hG x=⟨j,k⟩ ↔
      x=(splitIndex G hG).symm ⟨j,k⟩ := by
    constructor
    · intro h
      apply (splitIndex G hG).injective
      simpa using h
    · rintro rfl
      exact Equiv.apply_symm_apply _ _
  rw [SelfReduction.probability_congr he,SelfReduction.probability_eq_card]
  simp

/-- Conditional on a named selected partner, the carried residual rank is
exactly uniform. Hence the single initial rejection draw supports every
successive adaptive count-weighted choice without any approximation. -/
 theorem adaptive_conditional_uniform {N : ℕ} (G : MatrixGraph (N+1))
    (hG : DistanceHereditaryGraph G.graph) (j : Fin (N+1)) (k : Fin (weight G j)) :
    SelfReduction.probability (fun x : Fin (count ⟨N+1,G⟩) => splitIndex G hG x=⟨j,k⟩) /
      SelfReduction.probability (fun x : Fin (count ⟨N+1,G⟩) => (splitIndex G hG x).1=j)=
      1/(weight G j : ℚ) := by
  rw [adaptive_joint_probability G hG j k,branch_probability G hG j]
  have hk : (weight G j : ℚ)≠0 := by
    have hh := k.isLt
    exact_mod_cast (show weight G j≠0 by omega)
  have hc : (count ⟨N+1,G⟩ : ℚ)≠0 := by
    have hh := ((splitIndex G hG).symm ⟨j,k⟩).isLt
    exact_mod_cast (show count ⟨N+1,G⟩≠0 by omega)
  field_simp

/-- The machine is fixed, finite-control, and query-free. It uses unbounded
fresh fair coins; its finite-trace law and expected work are proved above. -/
 theorem finite_query_free_program : Main.program.QueryFree ∧0<Main.program.controlSize :=
  ⟨Main.queryFree,FairCode.controlSize_positive _⟩

end HiddenCircuits.ExactSampling
