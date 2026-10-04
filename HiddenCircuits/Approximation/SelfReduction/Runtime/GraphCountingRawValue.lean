import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountingValue
import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountSetup

/-! Total value of the raw general-graph counter: malformed, odd-order and
short-tape inputs produce canonical zero; accepted inputs use the real sampler. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
open Complexity SelfReduction.GraphCount

noncomputable def evaluate (raw : BitString) : BitString :=
  if GraphCountSetup.ready raw then
    match GraphInput.decode (GraphCountSetup.graph raw) with
    | none => encodeRatio 0 0
    | some G =>
      if he : G.1%2=0 then
        if hd : G.1≤GraphCountSetup.size raw then
          estimate (GraphCountSetup.size raw) G he hd (GraphCountSetup.coins raw)
        else encodeRatio 0 0
      else encodeRatio 0 0
  else encodeRatio 0 0

lemma evaluate_reject (raw : BitString) (hr : GraphCountSetup.ready raw=false) : evaluate raw=encodeRatio 0 0 := by
  simp [evaluate,hr]
lemma evaluate_accept (raw : BitString) (G : GraphInput) (hr : GraphCountSetup.ready raw=true)
    (hdec : GraphInput.decode (GraphCountSetup.graph raw)=some G) (he : G.1%2=0) (hd : G.1≤GraphCountSetup.size raw) :
    evaluate raw=estimate (GraphCountSetup.size raw) G he hd (GraphCountSetup.coins raw) := by
  simp [evaluate,hr,hdec,he,hd]

lemma evaluate_canonical (G : GraphInput) (r k : ℕ) (coins : BitString) (he : G.1%2=0)
    (hcoins : randomBitsPolynomial.eval (estimateInput G.encode r k).length≤coins.length) :
    evaluate (pairBits (estimateInput G.encode r k) coins)=
      estimate (estimateInput G.encode r k).length G he (GraphCountSetup.canonical_bounds G r k).1 coins := by
  have hr := GraphCountSetup.canonical_ready G r k coins he hcoins
  have hd := (GraphCountSetup.canonical_bounds G r k).1
  simpa only [GraphCountSetup.size_pair,GraphCountSetup.coins_pair] using evaluate_accept
    (pairBits (estimateInput G.encode r k) coins) G hr (by simp) he (by simpa using hd)

lemma evaluate_odd (G : GraphInput) (r k : ℕ) (coins : BitString) (he : G.1%2≠0) :
    evaluate (pairBits (estimateInput G.encode r k) coins)=encodeRatio 0 0 :=
  evaluate_reject _ (GraphCountSetup.canonical_odd G r k coins he)

end HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
