import HiddenCircuits.Approximation.SamplerRuntime.EndpointParserValidity

/-! Canonical decoding and its literal size
bound, derived from the all-input endpoint parser semantics. -/
namespace HiddenCircuits.GraphReduction.MonotoneEndpointEncoding
open Complexity

theorem encode_of_decode {xs : BitString} {E : Input} (h : decode xs=some E) : encode E=xs :=
  (Approximation.SamplerRuntime.EndpointParser.decode_reconstruct h).symm

theorem decode_some {xs : BitString} {E : Input} (h : decode xs=some E) : encode E=xs :=
  encode_of_decode h

theorem size_le_of_decode {xs : BitString} {E : Input} (h : decode xs=some E) : E.1≤xs.length := by
  rw [←encode_of_decode h]
  simp only [encode,encodeBitList_length,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,List.length_cons,List.length_nil,List.length_replicate]
  omega
end HiddenCircuits.GraphReduction.MonotoneEndpointEncoding
