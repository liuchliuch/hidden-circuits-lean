import HiddenCircuits.Approximation.SelfReduction.Runtime.CountValue
import HiddenCircuits.Approximation.SelfReduction.Runtime.CountSetup

/-! Total encoded counting function. Invalid syntax, invalid endpoint graphs or
insufficient random tapes receive exact zero; accepted inputs use only the
literal finite endpoint sampling/deletion experiment. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.MonotoneCount
open Complexity GraphReduction.MonotoneEndpointEncoding
open HiddenCircuits.Approximation.SelfReduction.EndpointResidual

noncomputable def evaluate (raw : BitString) : BitString :=
  if CountSetup.ready raw then
    match decode (CountSetup.graph raw) with
    | none => encodeRatio 0 0
    | some E =>
      if hd : E.1 ≤ CountSetup.size raw then
        endpointEstimate (CountSetup.size raw) E hd (CountSetup.coins raw)
      else encodeRatio 0 0
  else encodeRatio 0 0

 theorem evaluate_reject (raw : BitString) (hr : CountSetup.ready raw=false) : evaluate raw=encodeRatio 0 0 := by
  simp [evaluate,hr]

 theorem evaluate_accept (raw : BitString) (E : Input) (hr : CountSetup.ready raw=true)
    (he : decode (CountSetup.graph raw)=some E) (hd : E.1 ≤ CountSetup.size raw) :
    evaluate raw=endpointEstimate (CountSetup.size raw) E hd (CountSetup.coins raw) := by
  simp [evaluate,hr,he,hd]

 theorem evaluate_canonical (E : Input) (r k : ℕ) (coins : BitString)
    (hcoins : randomBitsPolynomial.eval (estimateInput (encode E) r k).length ≤ coins.length) :
    evaluate (pairBits (estimateInput (encode E) r k) coins)=
      endpointEstimate (estimateInput (encode E) r k).length E (CountSetup.canonical_bounds E r k).1 coins := by
  have hr := CountSetup.canonical_ready E r k coins hcoins
  have hd := (CountSetup.canonical_bounds E r k).1
  simpa only [CountSetup.size_pair,CountSetup.coins_pair] using evaluate_accept
    (pairBits (estimateInput (encode E) r k) coins) E hr (by simp) (by simpa using hd)

end HiddenCircuits.Approximation.SelfReduction.Runtime.MonotoneCount
