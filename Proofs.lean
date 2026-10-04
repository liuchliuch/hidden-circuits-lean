import HiddenCircuits
import HiddenCircuits.Complexity.IndependentSetCompleteness
import HiddenCircuits.Circuit.Runtime.ConstraintSourceReduction

/-! Proofs of the public statements for arXiv:2609.18132v1.
The numbering follows the paper. Graph-class completeness uses the explicit
promise contract in `ClassMatchingSharpPComplete`; the scope is documented in
`docs/paper.md`. All definitions referenced below belong to the audited library.
-/
namespace HiddenCircuits.Paper
set_option autoImplicit false
open HiddenCircuits HiddenCircuits.Complexity HiddenCircuits.Circuit.Runtime
open HiddenCircuits.GraphReduction HiddenCircuits.Approximation HiddenCircuits.DH
open Polynomial
open scoped BigOperators Kronecker
attribute [local instance] Classical.propDecidable

/-- Theorem 1.1. -/
theorem theorem_1_1 :
    ClassMatchingSharpPComplete (fun G => MonotoneGraph G.2.graph) ∧
    ClassMatchingSharpPComplete (fun G => RealUnitInterval.UnitIntervalGraph G.2.graph) ∧
    ClassMatchingSharpPComplete (fun G => ChordalPermutationGraph G.2.graph) ∧
    (∀ n (G : SimpleGraph (Fin n)), MonotoneGraph G ↔ BipartitePermutationGraph G) :=
  ⟨monotone_matching_sharpPComplete, realUnit_matching_sharpPComplete,
      private_matching_sharpPComplete, fun _ G => monotoneGraph_iff_bipartitePermutationGraph G⟩

/-- Corollary 1.2. -/
theorem corollary_1_2 :
    SharpPComplete MonotoneEndpointEncoding.count ∧
    HasFPAUS SamplerRuntime.Output.promised SamplerRuntime.Output.solutions ∧
    HasFPRAS SamplerRuntime.Output.promised MonotoneEndpointEncoding.count :=
  ⟨⟨monotoneEndpoint_count_sharpP, monotoneEndpoint_count_sharpPHard⟩,
      SamplerRuntime.MonotoneSampler.hasFPAUS, SelfReduction.Runtime.MonotoneCount.hasFPRAS⟩

/-- Corollary 1.3. -/
theorem corollary_1_3 :
    SharpPComplete unitCoordinateProblem ∧ UnitCoordinateOracle unitCoordinateProblem ∧
    HasFPAUS SamplerRuntime.CoordinateSampler.promised SamplerRuntime.CoordinateSampler.solutions ∧
    HasFPRAS SamplerRuntime.CoordinateSampler.promised unitCoordinateProblem :=
  ⟨⟨unitCoordinateProblem_sharpP, unitCoordinateProblem_sharpPHard⟩,
      unitCoordinateProblem_oracle, SamplerRuntime.CoordinateSampler.hasFPAUS,
      SelfReduction.Runtime.CoordinateCounting.hasFPRAS⟩

/-- Corollary 1.4. -/
theorem corollary_1_4 :
    ClassMatchingSharpPComplete (fun G => Quasimonotone G.2.graph) ∧
    HasFPAUS SamplerRuntime.GraphFunctional.promised SamplerRuntime.GraphFunctional.solutions ∧
    HasFPRAS SamplerRuntime.GraphFunctional.promised GraphInput.perfectMatchingProblem :=
  ⟨quasimonotone_matching_sharpPComplete, SamplerRuntime.GraphSampler.quasimonotone_hasFPAUS,
      SelfReduction.Runtime.GraphCounting.hasFPRAS⟩

/-- Definition 3.1 (evaluation identity). -/
theorem definition_3_1 (w : WordInstance) :
    w.value = wordMatrix w.particles w.word w.source w.target :=
  rfl

/-- Lemma 3.2. -/
theorem lemma_3_2 (w : WordInstance) :
    ∃ z : ℤ, w.value = (z : ℚ) ∧
      z.natAbs.size + 1 ≤ 14 * (2 * w.particles + w.word.length + 1)^5 :=
  w.value_bit_bound_tracks

/-- Lemma 3.3. -/
theorem lemma_3_3 :
    PolyTuringReduction WordEvalOracle.problem pairEval ∧
    (∀ (w : WordInstance) (hw : w.word ≠ []),
      (GraphReduction.Runtime.PairEval.WordSolver.samples w hw).length = w.word.length * w.particles^2 + 1) ∧
    (∀ (w : WordInstance) (hw : w.word ≠ [])
      (t : Fin (GraphReduction.Runtime.WordGraph.Recovery.degree w + 1)),
      (GraphReduction.Runtime.PairEval.WordQuery.sampleInput w hw t.val).pairs.length =
        w.word.length * (t.val + 1)) :=
  ⟨GraphReduction.Runtime.PairEval.WordReduction.wordEval_le_pairEval,
      GraphReduction.Runtime.PairEval.WordSolver.samples_length,
      GraphReduction.Runtime.PairEval.WordSolver.sample_pairs⟩

/-- Lemma 4.1. -/
theorem lemma_4_1 {n q : ℕ} (l : Letter n) (S T : State n q)
    (hn : l.matrix q S T ≠ 0) :
    (S.val.filter (fun x => x.val < l.index.val) =
      T.val.filter (fun x => x.val < l.index.val)) ∧
    ∀ c, T.prefixCount c ≤ S.prefixCount c +
      (match l.kind with
       | .R | .B => if c = l.index.val + 1 then 1 else 0
       | .D | .E => 0) :=
  HiddenCircuits.letter_flow l S T hn

/-- Lemma 4.2. -/
theorem lemma_4_2 {a b c : ℕ} (w : List (Letter b)) :
    (∀ q (S T : State (a + (b + c)) q),
      wordMatrix q (middleWord a c w) S T ≠ 0 → T.blockCount a b ≤ S.blockCount a b) ∧
    (∀ u v z (S₀ T₀ : State a u) (S₁ T₁ : State b v) (S₂ T₂ : State c z),
      wordMatrix (u + (v + z)) (middleWord a c w)
        (State.join S₀ (State.join S₁ S₂)) (State.join T₀ (State.join T₁ T₂)) =
        (if S₀ = T₀ then 1 else 0) * wordMatrix v w S₁ T₁ * (if S₂ = T₂ then 1 else 0)) :=
  HiddenCircuits.middleWord_restriction w

/-- Lemma 5.1. -/
theorem lemma_5_1 :
    localFilter 0 = 0 ∧ localFilter 1 = 0 ∧
    (∀ i j : Fin 6, localFilter 2 (Small.enum2 i) (Small.enum2 j) = Small.Theta2 i j) ∧
    localFilter 2 * localFilter 2 = localFilter 2 ∧ (localFilter 2).rank = 2 ∧
    (∀ T, localFilter 2 (Small.states2 1) T = if T = Small.states2 1 then 1 else 0) ∧
    (∀ T, localFilter 2 (Small.states2 3) T = if T = Small.states2 3 then 1 else 0) :=
  ⟨localFilter_zero, localFilter_one, localFilter_table, localFilter_idempotent,
      localFilter_rank, localFilter_fixes_zero, localFilter_fixes_one⟩

/-- Proposition 5.2. -/
theorem proposition_5_2 (k : ℕ) :
    globalProjection k * globalProjection k = globalProjection k ∧
    (globalProjection k).rank = 2^k ∧
    globalProjection k = ((1 / 64 : ℚ)^(k * globalProjectionExponent k)) •
      wordMatrix (2 * k) (globalProjectionWord k) ∧
    (globalProjectionWord k).length = 20 * k * (2 * k * (k - 1) + 2) ∧
    (globalProjectionWord k).length ≤ 40 * k^3 + 40 * k :=
  ⟨globalProjection_idempotent k, globalProjection_rank k, globalProjection_eq_word k,
      globalProjectionWord_length k, globalProjectionWord_length_bound k⟩

/-- Lemma 5.3. -/
theorem lemma_5_3 (k : ℕ) :
    (codeColumns k).transpose * globalProjection k * codeColumns k = 1 ∧
    encodingE k * encodingL k = 1 ∧ encodingL k * encodingE k = globalProjection k ∧
    (∀ w : List (Matrix (State (blockWidth k) (2 * k)) (State (blockWidth k) (2 * k)) ℚ),
      encodingE k * projectedWord (globalProjection k) w * encodingL k = (w.map encoded).prod) :=
  ⟨codeColumns_projection k, encodingEL k, encodingLE k, encoded_composition k⟩

/-- Lemma 5.4. -/
theorem lemma_5_4 (b r c : ℕ)
    (w : List (Letter (blockWidth (b + (r + c))))) (h : ∀ l ∈ w, ActiveMiddle b r c l) :
    encoded (wordMatrix (2 * (b + (r + c))) w) =
      logicalExtend b r c (encoded (wordMatrix (2 * r) (localizeMiddleWord b r c w h))) :=
  projected_locality_of_indices b r c w h

/-- Lemma 6.1. -/
theorem lemma_6_1 :
    oneBitEncoded [⟨.R, 0⟩] = !![1,0; 1,0] ∧
    oneBitEncoded [⟨.E, 0⟩] = !![1,1; 0,0] ∧
    oneBitEncoded [⟨.B, 1⟩] = !![2,0; 0,1] ∧
    oneBitEncoded [⟨.D, 2⟩] = !![-1,0; 0,1/2] ∧
    oneBitEncoded filterT = !![0,8; 8,0] ∧
    oneBitEncoded mixingWord = !![-2,4; 4,8] ∧
    oneBitEncoded [⟨.D, 2⟩] * oneBitEncoded mixingWord * oneBitEncoded [⟨.D, 2⟩] =
      (-2 : ℚ) • !![1,1; 1,-1] ∧
    twoBitEncoded [⟨.R, 3⟩] = !![-2,2,-7/2,-6; 0,-3,0,-2; 0,0,2,-4; 0,0,0,1] :=
  ⟨oneBit_R, oneBit_E, oneBit_Q, oneBit_A, oneBit_T, oneBit_mix, oneBit_H, twoBit_G⟩

/-- Lemma 7.1. -/
theorem lemma_7_1 : PolyTuringReduction deltaProblem WordEvalOracle.problem :=
  DeltaRawReduction.deltaEval_le_wordEval

/-- Lemma 7.2. -/
theorem lemma_7_2 : PolyTuringReduction constraintProblem deltaProblem :=
  ConstraintRawReduction.constraintEval_le_deltaEval

/-- Proposition 8.1. -/
theorem proposition_8_1 : PolyTuringReduction GraphInput.independentSetProblem constraintProblem :=
  ConstraintSource.independentSet_to_constraintEval

/-- Theorem 8.2. -/
theorem theorem_8_2 :
    PolyTuringReduction GraphInput.independentSetProblem WordEvalOracle.problem ∧
    PolyTuringReduction WordEvalOracle.problem pairEval ∧
    SharpPHard WordEvalOracle.problem ∧ SharpPHard pairEval :=
  ⟨WordEvalOracle.wordEval_sharpPHard _ GraphVerifier.Runtime.independentSet_sharpP,
      GraphReduction.Runtime.PairEval.WordReduction.wordEval_le_pairEval,
      WordEvalOracle.wordEval_sharpPHard, GraphReduction.Runtime.PairEval.WordSolver.pairEval_sharpPHard⟩

/-- Theorem 9.1. -/
theorem theorem_9_1 : ClassMatchingSharpPComplete (fun G => MonotoneGraph G.2.graph) :=
  monotone_matching_sharpPComplete

/-- Lemma 9.2. -/
theorem lemma_9_2 {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
    (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop) :
    ∃ Φ : ℚ[X], Φ.natDegree ≤ (Fintype.card X + Fintype.card Y) / 2 ∧
      (∀ s : ℕ, Φ.eval (s : ℚ) = (perfectMatchingCount (probeGraph R A B s) : ℚ) /
        (s.factorial : ℚ)^Fintype.card I) ∧
      Φ.eval (-1) = weightedBipartiteCount (probeWeight R A B) :=
  bipartiteProbe_identity R A B

/-- Lemma 9.3. -/
theorem lemma_9_3 {p : ℕ} (w : List (CutPair p)) (hw : w ≠ [])
    (S T : State (2 * p) p) (s : Fin (2 * p * w.length + 1)) :
    (retainedMonotoneDiagram (fun r => w.get r) S T s.val).graph =
      monotoneQueryGraph (fun r => w.get r) S T s.val ∧
    Nonempty (MonotoneOrdering (probeRelation (retainedQueryRelation (fun r => w.get r) S T)
      (retainedEvenAttachment S T) oddAttachment s.val)) ∧
    Fintype.card (ProbePart (RetainedEven p w.length S T) (Fin w.length) s.val ⊕
      ProbePart (OddVertex (2 * p) w.length) (Fin w.length) s.val) ≤ 4 * p * w.length * (w.length + 1) :=
  monotonePairQuery_valid w hw S T s

/-- Proposition 10.1. -/
theorem proposition_10_1 (g : BitString → ℕ)
    (hg : ClassMatchingOracle (fun G => UnitIntervalGraph G.2.graph) g) :
    PolyTuringReduction pairEval g :=
  GraphReduction.Runtime.PairEval.Reduction.pairEval_to_unitInterval g hg

/-- Lemma 10.2. -/
theorem lemma_10_2 {V I : Type*} [Fintype V] [Fintype I]
    (G : SimpleGraph V) (A : I → V → Prop) :
    ∃ Ψ : ℚ[X], Ψ.natDegree ≤ Fintype.card V / 2 ∧
      (∀ t : ℕ, Ψ.eval (2 * t : ℚ) = (perfectMatchingCount (cliqueProbeGraph G A (2 * t)) : ℚ) /
        (oddFactorial t : ℚ)^Fintype.card I) ∧
      Ψ.eval (-1) = weightedPerfectMatchingCount (cliqueProbeWeight G A) :=
  cliqueProbe_identity G A

/-- Theorem 10.3. -/
theorem theorem_10_3 :
    ClassMatchingSharpPComplete (fun G => RealUnitInterval.UnitIntervalGraph G.2.graph) :=
  realUnit_matching_sharpPComplete

/-- Corollary 10.4. -/
theorem corollary_10_4 :
    SharpPComplete strictIntegerProblem ∧ StrictIntegerOracle strictIntegerProblem :=
  ⟨⟨strictIntegerProblem_sharpP, strictIntegerProblem_sharpPHard⟩, strictIntegerProblem_oracle⟩

/-- Theorem 11.1. -/
theorem theorem_11_1 :
    ClassMatchingSharpPComplete (fun G => ChordalPermutationGraph G.2.graph) :=
  private_matching_sharpPComplete

/-- Lemma 11.2. -/
theorem lemma_11_2 {p h : ℕ} (pairs : Fin h → CutPair p) (s : ℕ) :
    (PrivateProbe.diagram pairs s).graph = PrivateProbe.queryGraph pairs s :=
  PrivateProbe.diagram_graph pairs s

/-- Lemma 11.3. -/
theorem lemma_11_3 {p h : ℕ} (pairs : Fin h → CutPair p)
    (S T : State (2 * p) p) (s : ℕ) :
    Chordal (PrivateProbe.retainedQueryGraph pairs S T s) :=
  PrivateProbe.retainedQueryGraph_chordal pairs S T s

/-- Lemma 12.1. -/
theorem lemma_12_1 :
    (∀ {V : Type} (G : SimpleGraph V), QuasiChains G → DistanceHereditaryGraph G) ∧
    DistanceHereditaryGraph (SimpleGraph.pathGraph 5) ∧ ¬QuasiChains (SimpleGraph.pathGraph 5) :=
  quasiChains_strict_distanceHereditary

/-- Theorem 12.2. -/
theorem theorem_12_2 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : DistanceHereditaryGraph G) (rows : Vector (List (Fin n)) n)
    (hr : DH.LinearBuckets.Adjacency.Represents G rows) (hn : ∀ v : Fin n, rows[v.val].Nodup) :
    ∃ es, (DH.LinearPreprocessing.preprocess G rows hr hn).value = some es ∧
      (DH.LinearPreprocessing.count G rows hr hn).value = some (perfectMatchingCount G : ℤ) ∧
      (DH.LinearPreprocessing.count G rows hr hn).preprocessing ≤ 2200 * (n + G.edgeFinset.card) ∧
      (DH.LinearPreprocessing.count G rows hr hn).arithmetic ≤ 36 * n.choose 2 + n ∧
      DH.ExecutionBits.ForestProperty (fun z => z.natAbs.size ≤ (3 * n + 3) * (n + 1).size + 2) es :=
  DH.LinearPreprocessing.count_spec G hG rows hr hn

/-- Lemma 12.3 (merge and finalization refinements). -/
theorem lemma_12_3 {V R : Type*} [Fintype V]
    {G : SimpleGraph V} {H : SimpleGraph R} (p : BoundaryPartition G H) :
    (∀ {u v : R} (ht : TwinPair H u v) (_hadj : H.Adj u v) (k : ℕ),
      Fintype.card (BagState ((p.twinMerge ht).fiberGraph ⟨u, ht.distinct⟩)
        ((p.twinMerge ht).fiberActive ⟨u, ht.distinct⟩) k) =
      Fintype.card (BagState
        (joinGraph (p.fiberGraph u) (p.fiberGraph v) (p.fiberActive u) (p.fiberActive v))
        {x | Sum.elim (p.fiberActive u) (p.fiberActive v) x} k)) ∧
    (∀ {u v : R} (ht : TwinPair H u v) (_hadj : ¬H.Adj u v) (k : ℕ),
      Fintype.card (BagState ((p.twinMerge ht).fiberGraph ⟨u, ht.distinct⟩)
        ((p.twinMerge ht).fiberActive ⟨u, ht.distinct⟩) k) =
      Fintype.card (BagState (disjointGraph (p.fiberGraph u) (p.fiberGraph v))
        {x | Sum.elim (p.fiberActive u) (p.fiberActive v) x} k)) ∧
    (∀ {u v : R} (hp : PendantPair H u v) (k : ℕ),
      Fintype.card (BagState ((p.pendantMerge hp).fiberGraph ⟨u, hp.distinct⟩)
        ((p.pendantMerge hp).fiberActive ⟨u, hp.distinct⟩) k) =
      Fintype.card (BagState
        (joinGraph (p.fiberGraph u) (p.fiberGraph v) (p.fiberActive u) (p.fiberActive v))
        {x | ∃ a ∈ p.fiberActive u, x = Sum.inl a} k)) ∧
    (∀ (u : R) (_hu : ∀ r, ¬H.Adj u r),
      perfectMatchingCount G = Fintype.card (BagState (p.fiberGraph u) (p.fiberActive u) 0) *
        perfectMatchingCount (p.remainingGraph u)) :=
  ⟨fun ht hadj k => p.twinMerge_join_count ht hadj k,
      fun ht hadj k => p.twinMerge_disjoint_count ht hadj k,
      fun hp k => p.pendantMerge_join_count hp k, p.finalize_count⟩

/-- Lemma 12.4. -/
theorem lemma_12_4 (F : ℤ[X]) :
    matchingColumn F 0 = F ∧ matchingColumn F 1 = Polynomial.X * F + derivative F ∧
    (∀ j, matchingColumn F (j + 2) = Polynomial.X * matchingColumn F (j + 1) +
      derivative (matchingColumn F (j + 1)) - (j + 1 : ℤ[X]) * matchingColumn F j) ∧
    (∀ (a b : ℕ) (input weights : Array ℤ), b ≤ a → 1 ≤ b →
      input.size ≤ a + 1 → weights.size ≤ b + 1 →
      DH.ArrayColumn.polynomial (DH.ArrayColumn.runWeighted (a + b + 1) input weights b).value.total =
        DH.ArrayColumn.trueTwinProduct (DH.ArrayColumn.polynomial input) (DH.ArrayColumn.polynomial weights) ∧
      (DH.ArrayColumn.runWeighted (a + b + 1) input weights b).operations ≤ 36 * a * b) :=
  ⟨matchingColumn_zero F, matchingColumn_one F, matchingColumn_recurrence F,
      fun a b input weights ha hb hf hg =>
        ⟨DH.ArrayColumn.runWeighted_product_of_size a b input weights hf hg,
          DH.ArrayColumn.runWeighted_cost_le_pair_charge a b input weights ha hb⟩⟩

/-- Exact-counting consequence. -/
theorem exact_counting_collapse :
    (∃ g : BitString → ℕ, FP g ∧ ClassMatchingOracle (fun G => MonotoneGraph G.2.graph) g) ↔ FP_eq_SharpP :=
  monotone_matching_sharpPComplete.fp_oracle_iff_collapse

/-- Independent-set source completeness. -/
theorem independent_set_complete :
    SharpPComplete GraphInput.independentSetProblem :=
  independentSet_sharpPComplete

/-- Supplied permutation representation. -/
theorem supplied_monotone :
    ∃ f : BitString → ℕ, SharpP f ∧ SharpPHard f ∧ SuppliedMonotonePermutationOracle f :=
  suppliedMonotone_has_sharpP_complete_extension

/-- Complete forest execution. -/
theorem bag_execution (es : List BagExpr) :
    (BagForest.execute es).value = (perfectMatchingCount (BagForest.graph es) : ℤ) :=
  BagForest.execute_correct es

/-- Polynomial binary time for distance-hereditary counting. -/
theorem dh_bit_time :
    PolyTime DH.BinaryRuntime.function ∧
    (∀ G : GraphInput, DistanceHereditaryGraph G.2.graph →
      DH.BinaryRuntime.function G.encode = Computability.encodeNat (perfectMatchingCount G.2.graph)) :=
  ⟨DH.BinaryRuntime.polyTime, DH.BinaryRuntime.distanceHereditary⟩

/-- Off-balanced projection regression. -/
theorem offbalanced_projection :
    twoBitProjection (twoBitCode 0) (Small.gate8States 61) = -8 :=
  HiddenCircuits.twoBitProjection_offbalanced_tail

/-- Polynomial equivalence of valid unit-interval input models. -/
theorem unit_input_models :
    PolyTime GraphReduction.Runtime.UnitCoordinateExtractionResult.result ∧
    PolyTime GraphReduction.Runtime.CoordinateGraph.bits ∧
    (∀ raw G, GraphInput.decode raw = some G → RealUnitInterval.UnitIntervalGraph G.2.graph →
      ∃ R : UnitIntegerRepresentation G,
        GraphReduction.Runtime.UnitCoordinateExtractionResult.result raw = unitCoordinateBits G R) ∧
    (∀ G (R : UnitIntegerRepresentation G),
      GraphReduction.Runtime.CoordinateGraph.bits (unitCoordinateBits G R) = G.encode) :=
  GraphReduction.Runtime.UnitInputModelEquivalence.polynomial_input_model_equivalence

/-- Exact uniform sampling with expected polynomial actual work. -/
theorem exact_sampling (G : GraphInput) (hG : DistanceHereditaryGraph G.2.graph)
    (hc : 0 < ExactSampling.DHWeights.count G) :
    ExactSampling.Runtime.Main.program.QueryFree ∧
    Function.Injective (ExactSampling.experimentWord hc) ∧
    (∀ a b : ExactSampling.CodedExperiment (ExactSampling.DHWeights.count G),
      (ExactSampling.experimentWord hc a).IsPrefix (ExactSampling.experimentWord hc b) → a = b) ∧
    (∑' t, ExactSampling.terminatingMass G t) = 1 ∧
    (∀ t (r : ExactSampling.DHIndex.Experiment G.2 t),
      ExactSampling.FairCode.Runs ExactSampling.Runtime.Main.program
        (ExactSampling.Runtime.Main.input G.encode)
        (ExactSampling.Runtime.Main.output (ExactSampling.Runtime.Main.sampledWord G.2 hG r.2))
        (ExactSampling.Runtime.FairDraw.fairReads hc t r.1 r.2)
        (ExactSampling.ActualWork.executionCost G hG hc t r)) ∧
    (∀ M : PerfectMatching G.2.graph,
      ∑' t, ExactSampling.outputMass G.2 hG M t = 1 / (perfectMatchingCount G.2.graph : ℝ)) ∧
    ExactSampling.ActualWork.expectedWork G hG hc ≤
      ((ExactSampling.expectedTimePolynomial.eval G.encode.length : ℕ) : ℝ) :=
  ExactSampling.ActualWork.exact_uniform_expected_sampler G hG hc

end HiddenCircuits.Paper
