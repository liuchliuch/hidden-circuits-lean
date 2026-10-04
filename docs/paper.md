# Paper correspondence

The reference is [arXiv:2609.18132v1](https://arxiv.org/abs/2609.18132v1), submitted on 16 September 2026. The checked original TeX has SHA-256 `082e8a8abf5181ed332cf309d57e00e9a1f73c75c756ddb6a1a2f0edc4b1cf54`.

The public interface covers all 32 numbered items. Theorem statements below use the library's explicit definitions; `Proofs.lean` supplies their proofs. Definition 3.1 is represented by `WordInstance` in `Transfers.lean`, with its evaluation identity exposed in the interface.

| Paper | Public statement | Main implementation |
| --- | --- | --- |
| Theorem 1.1 | [theorem_1_1](../Statements.lean#L21) | [GraphReduction/Runtime/MonotoneHardness](../HiddenCircuits/GraphReduction/Runtime/MonotoneHardness.lean), [GraphReduction/Runtime/CliqueGraphHardness](../HiddenCircuits/GraphReduction/Runtime/CliqueGraphHardness.lean) |
| Corollary 1.2 | [corollary_1_2](../Statements.lean#L29) | [GraphReduction/Runtime/MonotoneEndpointHardness](../HiddenCircuits/GraphReduction/Runtime/MonotoneEndpointHardness.lean), [Approximation/SamplerRuntime/MonotoneSampler](../HiddenCircuits/Approximation/SamplerRuntime/MonotoneSampler.lean) |
| Corollary 1.3 | [corollary_1_3](../Statements.lean#L36) | [GraphReduction/Runtime/UnitCoordinateHardness](../HiddenCircuits/GraphReduction/Runtime/UnitCoordinateHardness.lean), [GraphReduction/Runtime/UnitCoordinateMembership](../HiddenCircuits/GraphReduction/Runtime/UnitCoordinateMembership.lean) |
| Corollary 1.4 | [corollary_1_4](../Statements.lean#L43) | [GraphReduction/Runtime/CliqueGraphHardness](../HiddenCircuits/GraphReduction/Runtime/CliqueGraphHardness.lean), [Approximation/SamplerRuntime/GraphSampler](../HiddenCircuits/Approximation/SamplerRuntime/GraphSampler.lean) |
| Definition 3.1 | [definition_3_1](../Statements.lean#L50) | [Transfers](../HiddenCircuits/Transfers.lean), [Complexity/WordEncoding](../HiddenCircuits/Complexity/WordEncoding.lean) |
| Lemma 3.2 | [lemma_3_2](../Statements.lean#L55) | [BitBounds](../HiddenCircuits/BitBounds.lean), [Complexity/WordEncoding](../HiddenCircuits/Complexity/WordEncoding.lean) |
| Lemma 3.3 | [lemma_3_3](../Statements.lean#L61) | [GraphReduction/Runtime/PairEval/WordReduction](../HiddenCircuits/GraphReduction/Runtime/PairEval/WordReduction.lean), [GraphReduction/Runtime/PairEval/WordSolver](../HiddenCircuits/GraphReduction/Runtime/PairEval/WordSolver.lean) |
| Lemma 4.1 | [lemma_4_1](../Statements.lean#L72) | [FlowSupport](../HiddenCircuits/FlowSupport.lean), [FixedPrefix](../HiddenCircuits/FixedPrefix.lean) |
| Lemma 4.2 | [lemma_4_2](../Statements.lean#L83) | [BlockFlow](../HiddenCircuits/BlockFlow.lean), [BlockWords](../HiddenCircuits/BlockWords.lean) |
| Lemma 5.1 | [lemma_5_1](../Statements.lean#L93) | [FilterTheorem](../HiddenCircuits/FilterTheorem.lean) |
| Proposition 5.2 | [proposition_5_2](../Statements.lean#L102) | [GlobalRank](../HiddenCircuits/GlobalRank.lean), [GlobalProjectionWord](../HiddenCircuits/GlobalProjectionWord.lean) |
| Lemma 5.3 | [lemma_5_3](../Statements.lean#L112) | [RawCode](../HiddenCircuits/RawCode.lean), [Encoding](../HiddenCircuits/Encoding.lean) |
| Lemma 5.4 | [lemma_5_4](../Statements.lean#L120) | [CanonicalLocality](../HiddenCircuits/CanonicalLocality.lean) |
| Lemma 6.1 | [lemma_6_1](../Statements.lean#L127) | [OneBitGates](../HiddenCircuits/OneBitGates.lean), [TwoBitGates](../HiddenCircuits/TwoBitGates.lean) |
| Lemma 7.1 | [lemma_7_1](../Statements.lean#L140) | [Circuit/Runtime/DeltaRawReduction](../HiddenCircuits/Circuit/Runtime/DeltaRawReduction.lean), [Circuit/Runtime/DeltaWordRuntime](../HiddenCircuits/Circuit/Runtime/DeltaWordRuntime.lean) |
| Lemma 7.2 | [lemma_7_2](../Statements.lean#L144) | [Circuit/Runtime/ConstraintRawReduction](../HiddenCircuits/Circuit/Runtime/ConstraintRawReduction.lean), [Circuit/Runtime/SpectralConstraintDriver](../HiddenCircuits/Circuit/Runtime/SpectralConstraintDriver.lean) |
| Proposition 8.1 | [proposition_8_1](../Statements.lean#L148) | [Circuit/SourceCircuit](../HiddenCircuits/Circuit/SourceCircuit.lean), [Circuit/Runtime/ConstraintSourceReduction](../HiddenCircuits/Circuit/Runtime/ConstraintSourceReduction.lean) |
| Theorem 8.2 | [theorem_8_2](../Statements.lean#L152) | [Complexity/IndependentSetCompleteness](../HiddenCircuits/Complexity/IndependentSetCompleteness.lean), [Circuit/Runtime/WordEvalHardness](../HiddenCircuits/Circuit/Runtime/WordEvalHardness.lean) |
| Theorem 9.1 | [theorem_9_1](../Statements.lean#L159) | [GraphReduction/Runtime/MonotoneHardness](../HiddenCircuits/GraphReduction/Runtime/MonotoneHardness.lean), [GraphReduction/Runtime/MonotoneEndpointHardness](../HiddenCircuits/GraphReduction/Runtime/MonotoneEndpointHardness.lean) |
| Lemma 9.2 | [lemma_9_2](../Statements.lean#L163) | [GraphReduction/BipartiteProbe](../HiddenCircuits/GraphReduction/BipartiteProbe.lean), [GraphReduction/MonotoneReduction](../HiddenCircuits/GraphReduction/MonotoneReduction.lean) |
| Lemma 9.3 | [lemma_9_3](../Statements.lean#L172) | [GraphReduction/MonotoneQueryRepresentation](../HiddenCircuits/GraphReduction/MonotoneQueryRepresentation.lean), [GraphReduction/MonotoneReduction](../HiddenCircuits/GraphReduction/MonotoneReduction.lean) |
| Proposition 10.1 | [proposition_10_1](../Statements.lean#L183) | [GraphReduction/UnitIntervalReduction](../HiddenCircuits/GraphReduction/UnitIntervalReduction.lean), [GraphReduction/Runtime/PairEval/GraphReduction](../HiddenCircuits/GraphReduction/Runtime/PairEval/GraphReduction.lean) |
| Lemma 10.2 | [lemma_10_2](../Statements.lean#L189) | [GraphReduction/CliqueProbeIdentity](../HiddenCircuits/GraphReduction/CliqueProbeIdentity.lean), [GraphReduction/UnitIntervalRecovery](../HiddenCircuits/GraphReduction/UnitIntervalRecovery.lean) |
| Theorem 10.3 | [theorem_10_3](../Statements.lean#L198) | [GraphReduction/Runtime/CliqueGraphHardness](../HiddenCircuits/GraphReduction/Runtime/CliqueGraphHardness.lean), [GraphReduction/RealUnitIntervalsHardness](../HiddenCircuits/GraphReduction/RealUnitIntervalsHardness.lean) |
| Corollary 10.4 | [corollary_10_4](../Statements.lean#L203) | [GraphReduction/Runtime/StrictIntegerHardness](../HiddenCircuits/GraphReduction/Runtime/StrictIntegerHardness.lean), [GraphReduction/Runtime/StrictIntegerMembership](../HiddenCircuits/GraphReduction/Runtime/StrictIntegerMembership.lean) |
| Theorem 11.1 | [theorem_11_1](../Statements.lean#L208) | [GraphReduction/Runtime/CliqueGraphHardness](../HiddenCircuits/GraphReduction/Runtime/CliqueGraphHardness.lean), [GraphReduction/ChordalPermutationInterval](../HiddenCircuits/GraphReduction/ChordalPermutationInterval.lean) |
| Lemma 11.2 | [lemma_11_2](../Statements.lean#L213) | [GraphReduction/PrivateProbeDiagram](../HiddenCircuits/GraphReduction/PrivateProbeDiagram.lean), [GraphReduction/PrivateProbeRepresentation](../HiddenCircuits/GraphReduction/PrivateProbeRepresentation.lean) |
| Lemma 11.3 | [lemma_11_3](../Statements.lean#L218) | [GraphReduction/PrivateProbeChordal](../HiddenCircuits/GraphReduction/PrivateProbeChordal.lean), [GraphReduction/PrivateProbeReduction](../HiddenCircuits/GraphReduction/PrivateProbeReduction.lean) |
| Lemma 12.1 | [lemma_12_1](../Statements.lean#L224) | [DH/GraphClasses](../HiddenCircuits/DH/GraphClasses.lean) |
| Theorem 12.2 | [theorem_12_2](../Statements.lean#L230) | [DH/LinearPreprocessing](../HiddenCircuits/DH/LinearPreprocessing.lean), [DH/LayerExecutionCorrectness](../HiddenCircuits/DH/LayerExecutionCorrectness.lean) |
| Lemma 12.3 | [lemma_12_3](../Statements.lean#L241) | [DH/BagMatching](../HiddenCircuits/DH/BagMatching.lean), [DH/JoinCounts](../HiddenCircuits/DH/JoinCounts.lean) |
| Lemma 12.4 | [lemma_12_4](../Statements.lean#L266) | [DistanceHereditary](../HiddenCircuits/DistanceHereditary.lean), [DH/ArrayColumn](../HiddenCircuits/DH/ArrayColumn.lean) |

## Input and complexity conventions

`SharpP` counts fixed polynomial-length Boolean certificates accepted by actual finite TM2 programs. `PolyTuringReduction` requires all-input halting, exact binary output, and a uniform polynomial charge that includes the query and answer bit lengths. The independent-set source completeness theorem is proved within this development.

`ClassMatchingSharpPComplete` is the graph-class promise statement: a total #P extension exists, and every total oracle agreeing with matching counts on the promised graph encodings is #P-hard. It does not assert that every off-promise extension belongs to #P. Ordinary graph inputs use finite labeled, simple, unweighted adjacency matrices. The reductions construct valid graphs and representations; signed or negative interpolation values occur in exact postprocessing.

WordEval and circuit evaluation have signed integer or rational values, respectively. They are encoded as natural oracle answers. Their hardness statements do not assert that arbitrary signed or rational functions are #P counting functions. For the rational circuit encodings, the malformed-input sentinel zero is distinct from the encoding of a valid rational zero.

The coordinate interface uses signed integer numerators and one positive common denominator to describe equal-length closed intervals. The strict integer interface instead uses arbitrary positive integer radius and the condition `|x_u - x_v| < r`, including radius-one and equality boundaries. The permissive coordinate extensions can return one on a decoded empty list; their off-promise behavior differs from the ordinary recognition-gated unit-interval counter. Valid-input graph/coordinate conversion preserves the original labels; it is not a count-preserving reduction through the rejection sentinel on every malformed input.

When representations are supplied, graph-field #P extensions count the physically extracted graph. They do not validate the complete representation packet outside its promise. The supplied monotone endpoint-array and supplied two-line permutation-diagram interfaces are distinct, and both have concrete reduction programs.

For Lemmas 4.2 and 5.4, the interfaces express block restrictions and logical tensor locality through explicit state joins and index translations. The code states are compressed after applying the genuine global projection. A raw code row need not be fixed by that projection outside the balanced sector: the public off-balanced regression has value `-8`.

Lemma 12.3 is represented by the true-twin, false-twin, pendant, and finalization refinements, together with `bag_execution` and the complete ordinary-input algorithm in Theorem 12.2. The structural invariant is the `BoundaryPartition` type. Lemma 12.4 includes the literal polynomial recurrence and the executed array-product bound; the array algorithm orients the smaller child as `b ≤ a`.

The DH algorithm proves at most `2200(n+m)` graph accesses, `36 choose(n,2)+n` integer arithmetic operations, and an explicit `O(n log n)` bound for every observed numerical temporary. These are sparse graph-access and integer-arithmetic bounds, not quadratic bit complexity. A separate total [binary TM2 implementation](../HiddenCircuits/DH/BinaryRuntime.lean) establishes polynomial bit-time counting.

## Sampling and approximation

FPAUS and FPRAS use finite fair tapes whose lengths are polynomial in the original encoded request. FPAUS bounds total variation on the unconditional distribution, including failure. FPRAS uses relative error `1/(r+1)` and success probability at least `1-2^(-k)` with unary precision inputs; `k=2` gives confidence `3/4`. Zero-count promised inputs return zero on every tape. The initializer and runtime proofs are part of the development, rather than assumptions of the endpoints.

Exact DH sampling uses fresh unbounded fair bits and a fixed, finite, query-free program. Its complete experiment words are injective and prefix-free, terminating cylinders have total mass one, every matching has the exact uniform mass, and expected actual charged work is polynomial. Summability is proved explicitly. This is a finite-cylinder operational model; the development does not claim an infinite-product MeasureTheory interpreter or a probabilistic TM2 compiler.

## Additional public checks

- [exact_counting_collapse](../Statements.lean#L278): Exact-counting consequence.
- [independent_set_complete](../Statements.lean#L283): Independent-set source completeness.
- [supplied_monotone](../Statements.lean#L288): Supplied permutation representation.
- [bag_execution](../Statements.lean#L293): Complete forest execution.
- [dh_bit_time](../Statements.lean#L298): Polynomial binary time for distance-hereditary counting.
- [offbalanced_projection](../Statements.lean#L305): Off-balanced projection regression.
- [unit_input_models](../Statements.lean#L310): Polynomial equivalence of valid unit-interval input models.
- [exact_sampling](../Statements.lean#L321): Exact uniform sampling with expected polynomial actual work.

The map covers the numbered mathematical development and the listed computational consequences. Background literature, acknowledgments, and the historical graph-class diagram are not separate formalization claims. Compilation and Comparator results are reported in [validation.json](validation.json); neither replaces semantic review of these definitions and statements.
