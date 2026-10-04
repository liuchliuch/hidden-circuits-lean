import HiddenCircuits.ExactSampling.ExactMatching
import HiddenCircuits.ExactSampling.FairDeterminism

/-! Expected cost of actual terminating machine executions. The envelope is
used only to prove summability and bound this cost, not as its definition. -/
namespace HiddenCircuits.ExactSampling.ActualWork
open Complexity DH Approximation DHWeights Runtime Rejection
open scoped BigOperators
attribute [local instance] Classical.propDecidable

 theorem exists_execution (G : GraphInput) (hG : DistanceHereditaryGraph G.2.graph) (hc : 0<count G)
    (t : ℕ) (r : DHIndex.Experiment G.2 t) :
    ∃c,FairCode.Runs Main.program (Main.input G.encode)
      (Main.output (Main.sampledWord G.2 hG r.2)) (FairDraw.fairReads hc t r.1 r.2) c := by
  obtain ⟨c,hr,hb⟩ := Main.positive_runs G.2 hG hc t r.1 r.2
  exact ⟨c,hr⟩

/-- Actual charged execution length for a given complete fair-bit word. The
program is already fixed; this is a mathematical observation of its execution,
not an algorithm input or a supplied complexity certificate. -/
noncomputable def executionCost (G : GraphInput) (hG : DistanceHereditaryGraph G.2.graph) (hc : 0<count G)
    (t : ℕ) (r : DHIndex.Experiment G.2 t) : ℕ := Nat.find (exists_execution G hG hc t r)

 theorem executionCost_runs (G : GraphInput) (hG : DistanceHereditaryGraph G.2.graph) (hc : 0<count G)
    (t : ℕ) (r : DHIndex.Experiment G.2 t) :
    FairCode.Runs Main.program (Main.input G.encode) (Main.output (Main.sampledWord G.2 hG r.2))
      (FairDraw.fairReads hc t r.1 r.2) (executionCost G hG hc t r) :=
  Nat.find_spec (exists_execution G hG hc t r)

 theorem executionCost_le (G : GraphInput) (hG : DistanceHereditaryGraph G.2.graph) (hc : 0<count G)
    (t : ℕ) (r : DHIndex.Experiment G.2 t) : executionCost G hG hc t r≤workEnvelope G t := by
  obtain ⟨c,hr,hb⟩ := Main.positive_runs G.2 hG hc t r.1 r.2
  exact (Nat.find_min' (exists_execution G hG hc t r) hr).trans hb

/-- Every operational execution on this same random word has this exact
cost, so minimization in the definition cannot select an artificially cheap run. -/
 theorem executionCost_unique (G : GraphInput) (hG : DistanceHereditaryGraph G.2.graph) (hc : 0<count G)
    (t : ℕ) (r : DHIndex.Experiment G.2 t) (s : OracleBlock.Store 65) (c : ℕ)
    (h : FairCode.Runs Main.program (Main.input G.encode) s (FairDraw.fairReads hc t r.1 r.2) c) :
    c=executionCost G hG hc t r := h.cost_unique (executionCost_runs G hG hc t r)

/-- Sum of actual bit-work costs, each weighted by its exact fair-bit cylinder
probability. PrefixCodes proves these words are distinct and prefix-free. -/
noncomputable def expectedAt (G : GraphInput) (hG : DistanceHereditaryGraph G.2.graph) (hc : 0<count G)
    (t : ℕ) : ℝ :=
  (∑r : DHIndex.Experiment G.2 t,(executionCost G hG hc t r : ℝ)) /
    (2^((t+1)*width (count G)) : ℝ)

 theorem expectedAt_nonneg (G : GraphInput) (hG : DistanceHereditaryGraph G.2.graph) (hc : 0<count G)
    (t : ℕ) : 0≤expectedAt G hG hc t := by unfold expectedAt; positivity

 theorem expectedAt_le (G : GraphInput) (hG : DistanceHereditaryGraph G.2.graph) (hc : 0<count G)
    (t : ℕ) : expectedAt G hG hc t≤terminatingMass G t*(workEnvelope G t : ℝ) := by
  unfold expectedAt
  calc
    _ ≤ (∑_r : DHIndex.Experiment G.2 t,(workEnvelope G t : ℝ))/(2^((t+1)*width (count G)) : ℝ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply Finset.sum_le_sum
      intro r _
      exact_mod_cast executionCost_le G hG hc t r
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,terminatingMass,outcomeMass,
        DHIndex.Experiment,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
      ring

 theorem envelope_summable (G : GraphInput) (hc : 0<count G) :
    Summable (fun t => terminatingMass G t*(workEnvelope G t : ℝ)) := by
  have hmass := (outcomeMass_hasSum hc).mul_left (count G : ℝ)
  have hn : (count G : ℝ)≠0 := by exact_mod_cast hc.ne'
  have hmass' : HasSum (terminatingMass G) (1:ℝ) := by simpa [terminatingMass,hn] using hmass
  have htime := (weighted_attempts_hasSum hc).mul_left (120*((Nat.size (count G) : ℝ)+1))
  have h := (hmass'.mul_right ((Main.fixedTime.eval G.encode.length : ℕ) : ℝ)).add htime
  have he : (fun t => terminatingMass G t*(workEnvelope G t : ℝ))=
      (fun t => terminatingMass G t*((Main.fixedTime.eval G.encode.length : ℕ) : ℝ)+
        (120*((Nat.size (count G) : ℝ)+1))*(((t+1 : ℕ) : ℝ)*(count G : ℝ)*outcomeMass (count G) t)) := by
    funext t
    unfold terminatingMass workEnvelope
    push_cast
    ring
  rw [he]
  exact h.summable

 theorem expectedAt_summable (G : GraphInput) (hG : DistanceHereditaryGraph G.2.graph) (hc : 0<count G) :
    Summable (expectedAt G hG hc) :=
  Summable.of_nonneg_of_le (expectedAt_nonneg G hG hc) (expectedAt_le G hG hc) (envelope_summable G hc)

noncomputable def expectedWork (G : GraphInput) (hG : DistanceHereditaryGraph G.2.graph) (hc : 0<count G) : ℝ :=
  ∑'t,expectedAt G hG hc t

/-- Expected polynomial charged work of the actual finite fair-coin program,
measured in the original graph's binary input length. -/
 theorem expected_work_polynomial (G : GraphInput) (hG : DistanceHereditaryGraph G.2.graph) (hc : 0<count G) :
    expectedWork G hG hc≤((expectedTimePolynomial.eval G.encode.length : ℕ) : ℝ) := by
  apply le_trans _ (expected_polynomial_work G hG hc)
  exact (expectedAt_summable G hG hc).tsum_le_tsum (expectedAt_le G hG hc) (envelope_summable G hc)

 theorem quasiChains_expected_work_polynomial (G : GraphInput) (hG : QuasiChains G.2.graph) (hc : 0<count G) :
    expectedWork G (quasiChains_distanceHereditary hG) hc≤((expectedTimePolynomial.eval G.encode.length : ℕ) : ℝ) :=
  expected_work_polynomial G (quasiChains_distanceHereditary hG) hc

/-- One statement assembles the operational, coding, probabilistic and runtime
claims. There is no external sampler, count oracle, or runtime premise. -/
 theorem exact_uniform_expected_sampler (G : GraphInput) (hG : DistanceHereditaryGraph G.2.graph) (hc : 0<count G) :
    Main.program.QueryFree ∧
    Function.Injective (experimentWord hc) ∧
    (∀a b : CodedExperiment (count G), (experimentWord hc a).IsPrefix (experimentWord hc b)→a=b) ∧
    (∑'t,terminatingMass G t)=1 ∧
    (∀t (r : DHIndex.Experiment G.2 t),FairCode.Runs Main.program (Main.input G.encode)
      (Main.output (Main.sampledWord G.2 hG r.2)) (FairDraw.fairReads hc t r.1 r.2)
      (executionCost G hG hc t r)) ∧
    (∀M : PerfectMatching G.2.graph,∑'t,outputMass G.2 hG M t=1/(perfectMatchingCount G.2.graph : ℝ)) ∧
    expectedWork G hG hc≤((expectedTimePolynomial.eval G.encode.length : ℕ) : ℝ) :=
  ⟨Main.queryFree,experimentWord_injective hc,experimentWord_prefix_free hc,
    almost_sure_termination G hc,executionCost_runs G hG hc,exact_uniform G.2 hG,
    expected_work_polynomial G hG hc⟩

end HiddenCircuits.ExactSampling.ActualWork
