import HiddenCircuits.Approximation.CanonicalPaths.ComponentMaximum
import HiddenCircuits.Approximation.CanonicalPaths.ComponentStage

/-! The actual component stage: no cycle presentation, route, or mixing
certificate is a hypothesis. -/
namespace HiddenCircuits.Approximation.CanonicalPaths.UnionReconstruction
open LocalRoutes
variable {n : ℕ}

theorem actual_component_stage (E : MonotoneEndpoints n)
    (P Q : State (fun col row => Allowed E row col)) (active : Fin n)
    (hrep : componentMin P.val Q.val active=active) (hne : P.val active≠Q.val active) :
    ∃l<8*n*n+4,MarkedRoute Finset.univ
      (fun z => HasCompanion P Q z 6 ∧ Interrupted P.val Q.val z.val active)
      (phaseState P Q active.val) (phaseState P Q (active.val+1)) l := by
  obtain ⟨l,hl,hr⟩ := restricted_component_route E P Q active hne
  have hm := componentPeriod_le P.val Q.val active
  have hb : componentPeriod P.val Q.val active * componentPeriod P.val Q.val active ≤ n*n :=
    Nat.mul_self_le_mul_self hm
  exact ⟨l,by nlinarith,component_stage_of_route E P Q active hrep hr⟩

end HiddenCircuits.Approximation.CanonicalPaths.UnionReconstruction
