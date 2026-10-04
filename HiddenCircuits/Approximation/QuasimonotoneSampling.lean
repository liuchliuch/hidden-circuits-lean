import HiddenCircuits.Approximation.Quasimonotone.CanonicalFlow

/-!
# Concrete finite-bit sampling for quasimonotone and equal-length interval graphs

The graph property is used only to prove the actual switch experiment mixes.
The experiment never asks for a cut ordering, canonical path, or congestion
certificate. Matching initialization and finite-machine compilation are separate.
-/
namespace HiddenCircuits.Approximation.QuasimonotoneSampling
open QuasimonotoneProof FiniteChains GraphReduction
attribute [local instance] Classical.propDecidable

/-- This computable budget depends only on vertex count and unary accuracy. -/
def steps (n k : ℕ) : ℕ :=
  2*max 1 (partnerRouteLength n*(8*(n+1)^2)*partnerTrafficFactor n)*(n^2+2*k)

def bits (n k : ℕ) : ℕ := (1+(Nat.size n+Nat.size n))*steps n k

/-- The literal fair-bit experiment on actual undirected perfect matchings. -/
def sample {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ)
    (s : PerfectPartner G) (r : CoinTape (bits n k)) : PerfectPartner G :=
  runCoins (PartnerSwitch.step G (Nat.size n)) (steps n k) s r

/-- All-events error, with no assumed rapid mixing or path-existence result. -/
theorem sample_event_error {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : Quasimonotone G) (k : ℕ) (s : PerfectPartner G) (A : PerfectPartner G → Prop) :
    |coinProbability (bits n k) (fun r => A (sample G k s r)) -
      (Fintype.card {x : PerfectPartner G // A x} : ℚ)/Fintype.card (PerfectPartner G)| ≤ 1/(2^k : ℚ) := by
  letI : Nonempty (PerfectPartner G) := ⟨s⟩
  have h := runCoins_event_error (PartnerSwitch.step G (Nat.size n))
    (PartnerSwitch.step_involutive G (Nat.size n)) (PartnerSwitch.step_lazy G (Nat.size n))
    (quasimonotoneCanonicalPaths G hG) (n^2) k (PartnerSwitch.card_states_le G) s A
  simpa only [bits,steps,sample,FiniteChains.CanonicalPaths.mixingSteps,FiniteChains.CanonicalPaths.scale] using h

/-- Explicit polynomial bound on the number of literal fair bits. -/
theorem bits_le (n k : ℕ) :
    bits n k ≤ (1+2*n)*(2*(1+partnerRouteLength n*(8*(n+1)^2)*partnerTrafficFactor n)*(n^2+2*k)) := by
  have hw := FiniteChains.MonotoneSwitch.proposal_width_le (n := n)
  have hs : max 1 (partnerRouteLength n*(8*(n+1)^2)*partnerTrafficFactor n) ≤
      1+partnerRouteLength n*(8*(n+1)^2)*partnerTrafficFactor n := by omega
  unfold bits steps
  apply Nat.mul_le_mul
  · omega
  · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hs)

/-- Equal-length interval graphs inherit this actual finite-coin guarantee. -/
theorem unitInterval_sample_event_error {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (repr : GraphReduction.UnitInterval.Representation G) (k : ℕ) (s : PerfectPartner G) (A : PerfectPartner G → Prop) :
    |coinProbability (bits n k) (fun r => A (sample G k s r)) -
      (Fintype.card {x : PerfectPartner G // A x} : ℚ)/Fintype.card (PerfectPartner G)| ≤ 1/(2^k : ℚ) :=
  sample_event_error G (HiddenCircuits.Approximation.UnitInterval.Representation.quasimonotone repr) k s A

end HiddenCircuits.Approximation.QuasimonotoneSampling
