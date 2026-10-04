import HiddenCircuits.Approximation.Initialization.RawBudget
import HiddenCircuits.Approximation.SamplerRuntime.PartnerRunnerCorrectness
import HiddenCircuits.Approximation.SamplerRuntime.GraphDecode

/-! Raw general-graph sampler semantics and unconditional probability bridge.
Its finite-machine realization is supplied separately, never postulated. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.GraphFunctional
open Complexity GraphReduction Polynomial FiniteChains
open Initialization.RawExtraction
attribute [local instance] Classical.propDecidable

noncomputable def core {n : ℕ} (G : MatrixGraph n) (N : ℕ) (tape : BitString) : BitString :=
  PartnerRunner.afterInitialize G N (initialPartner G N (TapeRead.takePadded (3*N^4) tape)) (tape.drop (3*N^4))
noncomputable def evaluate (raw : BitString) : BitString :=
  match unpairBits raw with
  | none => []
  | some (input,tape) =>
    match unpairBits input with
    | none => []
    | some (graph,precision) =>
      if precision.all id then
        match GraphInput.decode graph with
        | none => []
        | some G => core G.2 (input.length+1) tape
      else []

def promised (xs : BitString) : Prop := ∃G : GraphInput,G.encode=xs ∧ Quasimonotone G.2.graph
noncomputable def solutions (xs : BitString) : Finset BitString :=
  match GraphInput.decode xs with | none => ∅ | some G => PartnerOutput.witnesses G.2
@[simp] lemma solutions_encode (G : GraphInput) : solutions G.encode=PartnerOutput.witnesses G.2 := by simp [solutions]

lemma core_sound {n : ℕ} (G : MatrixGraph n) (N : ℕ) (tape w : BitString)
    (h : decodeSample (core G N tape)=some w) : w∈PartnerOutput.witnesses G :=
  PartnerRunner.initialized_sound G N _ _ w h
lemma core_empty {n : ℕ} (G : MatrixGraph n) (N : ℕ) (tape : BitString)
    (h : PartnerOutput.witnesses G=∅) : decodeSample (core G N tape)=none :=
  PartnerRunner.initialized_empty G N _ _ h

lemma initialization_budget {n N : ℕ} (h:n≤N) : randomBits n N≤3*N^4 := by
  unfold randomBits
  have hm:=Nat.mul_le_mul (Nat.pow_le_pow_left h 3) (show 2*n+N≤3*N by omega)
  nlinarith

theorem core_event_error {n : ℕ} (G : MatrixGraph n) (hG : Quasimonotone G.graph) (N k : ℕ)
    (hn:n≤N) (hk:k+1≤N) (A : Option BitString → Prop) :
    |coinProbability (3*N^4+PartnerBudget.bits N) (fun r => A (decodeSample (core G N (List.ofFn r))))-
      uniformProbability (PartnerOutput.witnesses G) A|≤1/(2^k:ℚ) := by
  have hh := PartnerRunner.initialized_event_error G hG N k (3*N^4) hn hk
    (fun r => initialPartner G N (List.ofFn r))
    (fun h => by
      obtain ⟨P⟩ := h
      exact initialPartner_failure G N (3*N^4) (initialization_budget hn) ⟨P.toMatching⟩) A
  have he (r : CoinTape (3*N^4+PartnerBudget.bits N)) :
      core G N (List.ofFn r)=PartnerRunner.afterInitialize G N
        (initialPartner G N (List.ofFn (splitTape (3*N^4) (PartnerBudget.bits N) r).1))
        (List.ofFn (splitTape (3*N^4) (PartnerBudget.bits N) r).2) := by
    rw [core,TapeRead.prefix_eq_take _ _ (by simp),CoinLists.splitTape_take,CoinLists.splitTape_drop]
    rfl
  simpa only [he] using hh

lemma evaluate_canonical (G : GraphInput) (k : ℕ) (tape : BitString) :
    evaluate (pairBits (sampleInput G.encode k) tape)=core G.2 ((sampleInput G.encode k).length+1) tape := by
  simp [evaluate,sampleInput]

noncomputable def bitsPolynomial : Polynomial ℕ := 3*(X+1)^4+PartnerBudget.bitsPolynomial.comp (X+1)
lemma bits_eval (L : ℕ) : bitsPolynomial.eval L=3*(L+1)^4+PartnerBudget.bits (L+1) := by simp [bitsPolynomial]
noncomputable def randomProgram (h : PolyTime evaluate) : RandomBitProgram where
  evaluate := evaluate
  polynomialTime := h
  randomBits := bitsPolynomial
lemma bits_eq (h : PolyTime evaluate) (input : BitString) :
    (randomProgram h).bits input=3*(input.length+1)^4+PartnerBudget.bits (input.length+1) := bits_eval _
lemma run_canonical (h : PolyTime evaluate) (G : GraphInput) (k : ℕ)
    (r : CoinTape ((randomProgram h).bits (sampleInput G.encode k))) :
    (randomProgram h).run (sampleInput G.encode k) r=core G.2 ((sampleInput G.encode k).length+1) (List.ofFn r) :=
  evaluate_canonical G k _

theorem samplingGuarantee (h : PolyTime evaluate) : SamplingGuarantee (randomProgram h) promised solutions := by
  intro x hx k
  obtain ⟨G,rfl,hG⟩ := hx
  let N := (sampleInput G.encode k).length+1
  have hn:G.1≤N:=by
    have hh:=GraphInput.decode_vertices_bound (GraphInput.decode_encode G)
    dsimp[N];rw[sampleInput_length];omega
  have hk:k+1≤N:=by dsimp[N];rw[sampleInput_length];omega
  refine ⟨?_,?_,?_⟩
  · intro r w hw
    rw [run_canonical] at hw
    rw [solutions_encode]
    exact core_sound G.2 N _ w hw
  · intro he r
    rw [solutions_encode] at he
    rw [run_canonical]
    exact core_empty G.2 N _ he
  · intro A
    have hh:=core_event_error G.2 hG N k hn hk A
    simp only [solutions_encode,run_canonical]
    rw [bits_eq]
    exact hh
end HiddenCircuits.Approximation.SamplerRuntime.GraphFunctional
