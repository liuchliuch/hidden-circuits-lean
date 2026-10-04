import HiddenCircuits.Approximation.Quasimonotone.PartnerFlow
import HiddenCircuits.Approximation.Quasimonotone.PartnerKernel
namespace HiddenCircuits.Approximation.QuasimonotoneProof
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : Quasimonotone G)
noncomputable def quasimonotoneCanonicalPaths :
    FiniteChains.CanonicalPaths (PartnerSwitch.chain G (Nat.size n))
      (partnerTrafficFactor n) (partnerRouteLength n) (8*(n+1)^2) where
  path := partnerFlowPath G hG
  length_le := partnerFlowPath_length G hG
  traffic_le := partnerFlowPath_traffic G hG
  Q_pos := by positivity
  transition_lower P Q i := PartnerSwitch.move_chain_lower G (partnerFlowPath_move G hG P Q i)
end HiddenCircuits.Approximation.QuasimonotoneProof
