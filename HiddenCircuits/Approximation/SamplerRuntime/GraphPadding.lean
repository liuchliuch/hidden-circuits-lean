import HiddenCircuits.Approximation.SamplerRuntime.GraphFunctional

/-! Fixed global random-tape padding for the actual general-graph sampler.
Extra tape suffixes are ignored after the initializer and switch-chain budgets.
The resulting all-events bound includes initialization failure and empty inputs. -/
namespace HiddenCircuits.Approximation.SamplerRuntime
open Complexity GraphReduction FiniteChains
attribute [local instance] Classical.propDecidable

namespace PartnerIteration
variable {n : ℕ}

lemma iterate_take (G : MatrixGraph n) (t : ℕ) (P : PerfectPartner G.graph) (xs : BitString)
    (h : width n*t ≤ xs.length) : iterate G t P xs=iterate G t P (xs.take (width n*t)) := by
  calc
    iterate G t P xs=iterate G t P (xs.take (width n*t)++xs.drop (width n*t)) := by
      rw [List.take_append_drop]
    _ = _ := iterate_append G t P _ _ (by simp [List.length_take,min_eq_left h])

lemma iterate_append_of_le (G : MatrixGraph n) (t : ℕ) (P : PerfectPartner G.graph)
    (xs ys : BitString) (h : width n*t ≤ xs.length) :
    iterate G t P (xs++ys)=iterate G t P xs := by
  calc
    _ = iterate G t P ((xs++ys).take (width n*t)) := iterate_take G t P _ (by simp;omega)
    _ = iterate G t P (xs.take (width n*t)) := by rw [List.take_append_of_le_length h]
    _ = iterate G t P xs := (iterate_take G t P xs h).symm

end PartnerIteration

namespace PartnerRunner

lemma afterInitialize_append {n : ℕ} (G : MatrixGraph n) (N : ℕ)
    (start : Option (PerfectPartner G.graph)) (xs ys : BitString)
    (h : PartnerIteration.width n*PartnerBudget.steps N ≤ xs.length) :
    afterInitialize G N start (xs++ys)=afterInitialize G N start xs := by
  cases start with
  | none => rfl
  | some P => simp only [afterInitialize,evaluate,PartnerIteration.iterate_append_of_le G _ P xs ys h]

end PartnerRunner

namespace GraphPadding

/-- The actual core ignores every suffix beyond its fixed polynomial budget. -/
theorem core_append {n : ℕ} (G : MatrixGraph n) (N : ℕ) (hn : n ≤ N)
    (coins padding : BitString) (h : 3*N^4+PartnerBudget.bits N ≤ coins.length) :
    GraphFunctional.core G N (coins++padding)=GraphFunctional.core G N coins := by
  have hi : 3*N^4 ≤ coins.length := by omega
  have ht : 3*N^4 ≤ (coins++padding).length := by simp;omega
  have hm : PartnerIteration.width n*PartnerBudget.steps N ≤ (coins.drop (3*N^4)).length := by
    have hh := PartnerBudget.tape_budget hn
    simp only [PartnerIteration.width,List.length_drop] at *
    omega
  simp only [GraphFunctional.core,TapeRead.prefix_eq_take _ _ hi,TapeRead.prefix_eq_take _ _ ht,
    List.take_append_of_le_length hi,List.drop_append_of_le_length hi]
  exact PartnerRunner.afterInitialize_append G N _ _ _ hm

/-- Restricting an arbitrarily longer tape leaves the core output exactly unchanged. -/
theorem core_take {n : ℕ} (G : MatrixGraph n) (N : ℕ) (hn : n ≤ N)
    (coins : BitString) (h : 3*N^4+PartnerBudget.bits N ≤ coins.length) :
    GraphFunctional.core G N coins=
      GraphFunctional.core G N (coins.take (3*N^4+PartnerBudget.bits N)) := by
  calc
    _ = GraphFunctional.core G N
        (coins.take (3*N^4+PartnerBudget.bits N)++coins.drop (3*N^4+PartnerBudget.bits N)) := by
      rw [List.take_append_drop]
    _ = _ := core_append G N hn _ _ (by simp [List.length_take,min_eq_left h])

/-- Pointwise coupling of a long fair tape with its canonical prefix. -/
theorem core_ofFn_restrict {n : ℕ} (G : MatrixGraph n) (N m : ℕ) (hn : n ≤ N)
    (h : 3*N^4+PartnerBudget.bits N ≤ m) (r : CoinTape m) :
    GraphFunctional.core G N (List.ofFn r)=
      GraphFunctional.core G N (List.ofFn (CoinLists.restrictTape h r)) := by
  rw [CoinLists.restrict_ofFn]
  exact core_take G N hn _ (by simpa only [List.length_ofFn] using h)

/-- Fixed globally padded fair tapes preserve the unconditional all-events law. -/
theorem core_event_error {n : ℕ} (G : MatrixGraph n) (hG : Quasimonotone G.graph)
    (N k m : ℕ) (hn : n ≤ N) (hk : k+1 ≤ N) (h : 3*N^4+PartnerBudget.bits N ≤ m)
    (A : Option BitString → Prop) :
    |coinProbability m (fun r => A (decodeSample (GraphFunctional.core G N (List.ofFn r))))-
      uniformProbability (PartnerOutput.witnesses G) A| ≤ 1/(2^k:ℚ) := by
  simp_rw [core_ofFn_restrict G N m hn h]
  rw [CoinLists.probability_restrict h
    (fun r => A (decodeSample (GraphFunctional.core G N (List.ofFn r))))]
  exact GraphFunctional.core_event_error G hG N k hn hk A

lemma size_bounds (G : GraphInput) (k : ℕ) :
    G.1 ≤ (sampleInput G.encode k).length+1 ∧ k+1 ≤ (sampleInput G.encode k).length+1 := by
  have hh := GraphInput.decode_vertices_bound (GraphInput.decode_encode G)
  rw [sampleInput_length]
  omega

/-- Canonical raw input is unchanged by every surplus coin suffix. -/
theorem evaluate_append (G : GraphInput) (k : ℕ) (coins padding : BitString)
    (h : 3*((sampleInput G.encode k).length+1)^4+
      PartnerBudget.bits ((sampleInput G.encode k).length+1) ≤ coins.length) :
    GraphFunctional.evaluate (pairBits (sampleInput G.encode k) (coins++padding))=
      GraphFunctional.evaluate (pairBits (sampleInput G.encode k) coins) := by
  rw [GraphFunctional.evaluate_canonical,GraphFunctional.evaluate_canonical]
  exact core_append G.2 _ (size_bounds G k).1 coins padding h

/-- Canonical raw calls consume only their fixed prefix of a globally padded tape. -/
theorem evaluate_ofFn_restrict (G : GraphInput) (k m : ℕ)
    (h : 3*((sampleInput G.encode k).length+1)^4+
      PartnerBudget.bits ((sampleInput G.encode k).length+1) ≤ m) (r : CoinTape m) :
    GraphFunctional.evaluate (pairBits (sampleInput G.encode k) (List.ofFn r))=
      GraphFunctional.evaluate (pairBits (sampleInput G.encode k) (List.ofFn (CoinLists.restrictTape h r))) := by
  rw [GraphFunctional.evaluate_canonical,GraphFunctional.evaluate_canonical]
  exact core_ofFn_restrict G.2 _ m (size_bounds G k).1 h r

/-- Padded raw graph sampling, retaining its failure mass and zero-count semantics. -/
theorem event_error (G : GraphInput) (hG : Quasimonotone G.2.graph) (k m : ℕ)
    (h : 3*((sampleInput G.encode k).length+1)^4+
      PartnerBudget.bits ((sampleInput G.encode k).length+1) ≤ m) (A : Option BitString → Prop) :
    |coinProbability m (fun r => A (decodeSample (GraphFunctional.evaluate
      (pairBits (sampleInput G.encode k) (List.ofFn r)))))-
      uniformProbability (GraphFunctional.solutions G.encode) A| ≤ 1/(2^k:ℚ) := by
  simp only [GraphFunctional.evaluate_canonical,GraphFunctional.solutions_encode]
  exact core_event_error G.2 hG _ k m (size_bounds G k).1 (size_bounds G k).2 h A

/-- Every successful padded output is a genuine perfect-partner witness. -/
theorem evaluate_sound (G : GraphInput) (k : ℕ) (tape w : BitString)
    (h : decodeSample (GraphFunctional.evaluate (pairBits (sampleInput G.encode k) tape))=some w) :
    w∈GraphFunctional.solutions G.encode := by
  rw [GraphFunctional.evaluate_canonical] at h
  rw [GraphFunctional.solutions_encode]
  exact GraphFunctional.core_sound G.2 _ tape w h

/-- Zero-solution inputs always fail, for every tape and without conditioning. -/
theorem evaluate_empty (G : GraphInput) (k : ℕ) (tape : BitString)
    (h : GraphFunctional.solutions G.encode=∅) :
    decodeSample (GraphFunctional.evaluate (pairBits (sampleInput G.encode k) tape))=none := by
  rw [GraphFunctional.evaluate_canonical]
  rw [GraphFunctional.solutions_encode] at h
  exact GraphFunctional.core_empty G.2 _ tape h

end GraphPadding
end HiddenCircuits.Approximation.SamplerRuntime
