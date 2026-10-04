import HiddenCircuits.Approximation.SamplerRuntime.Core

/-! Total raw-input semantics and the
unconditional finite-coin probability bridge. The machine implementation is
constructed in the outer runtime modules, rather than assumed here. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.Functional
open Complexity GraphReduction.MonotoneEndpointEncoding FiniteChains
attribute [local instance] Classical.propDecidable

def evaluate (raw : BitString) : BitString :=
  match unpairBits raw with
  | none => []
  | some (input,tape) =>
    match unpairBits input with
    | none => []
    | some (graph,precision) =>
      if precision.all id then
        match decode graph with
        | none => []
        | some E => Core.evaluate E.2 input.length tape
      else []

lemma size_le_encode (E : Input) : E.1≤(encode E).length := by
  simp only [encode,encodeBitList_length,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,List.length_cons,List.length_nil,List.length_replicate]
  omega

@[simp] theorem evaluate_canonical (E : Input) (k : ℕ) (tape : BitString) :
    evaluate (pairBits (sampleInput (encode E) k) tape)=
      Core.evaluate E.2 (sampleInput (encode E) k).length tape := by
  simp [evaluate,sampleInput]

lemma evaluate_bad_outer {raw : BitString} (h : unpairBits raw=none) : evaluate raw=[] := by
  simp [evaluate,h]
lemma evaluate_bad_input (input tape : BitString) (h : unpairBits input=none) :
    evaluate (pairBits input tape)=[] := by simp [evaluate,h]
lemma evaluate_bad_precision (graph precision tape : BitString) (h : precision.all id=false) :
    evaluate (pairBits (pairBits graph precision) tape)=[] := by simp [evaluate,h]
lemma evaluate_bad_endpoints (graph precision tape : BitString) (h : decode graph=none) :
    evaluate (pairBits (pairBits graph precision) tape)=[] := by
  simp [evaluate,h]

noncomputable def randomProgram (h : PolyTime evaluate) : RandomBitProgram where
  evaluate := evaluate
  polynomialTime := h
  randomBits := Budget.bitsPolynomial

lemma bits_eq (h : PolyTime evaluate) (input : BitString) :
    (randomProgram h).bits input=Budget.bits input.length := Budget.bits_eval _
lemma run_canonical (h : PolyTime evaluate) (E : Input) (k : ℕ)
    (r : CoinTape ((randomProgram h).bits (sampleInput (encode E) k))) :
    (randomProgram h).run (sampleInput (encode E) k) r=
      Core.evaluate E.2 (sampleInput (encode E) k).length (List.ofFn r) :=
  evaluate_canonical E k _

end HiddenCircuits.Approximation.SamplerRuntime.Functional
