import HiddenCircuits.Approximation.CanonicalPaths.ActualComponentStage
namespace HiddenCircuits.Approximation.CanonicalPaths
open LocalRoutes UnionReconstruction
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (E : MonotoneEndpoints n)
  (P Q : State (fun col row => Allowed E row col))
def TrafficGood (z : State (fun col row => Allowed E row col)) : Prop :=
  ∃ active : Fin n, Interrupted P.val Q.val z.val active ∧ HasCompanion P Q z 6
theorem phase_good (active : Fin n) : TrafficGood E P Q (phaseState P Q active.val) := by
  refine ⟨active,fun _ _ => rfl,phaseState Q P active.val,∅,by simp,?_⟩
  intro i _
  exact phase_complement P.val Q.val active.val i
theorem stage_marked_route (active : Fin n) :
    ∃ l ≤ 8*n*n+4, MarkedRoute Finset.univ (TrafficGood E P Q)
      (phaseState P Q active.val) (phaseState P Q (active.val+1)) l := by
  by_cases hrep : componentMin P.val Q.val active=active
  · by_cases hfix : P.val active=Q.val active
    · have he : phaseState P Q (active.val+1)=phaseState P Q active.val :=
        Subtype.ext (phase_unchanged_fixed P.val Q.val active hfix)
      rw [he]
      exact ⟨0,Nat.zero_le _,MarkedRoute.nil _ (phase_good E P Q active)⟩
    · obtain ⟨l,hl,hr⟩ := actual_component_stage E P Q active hrep hfix
      exact ⟨l,hl.le,hr.mono (Finset.Subset.refl _) (fun z h => ⟨active,h.2,h.1⟩)⟩
  · have he : phaseState P Q (active.val+1)=phaseState P Q active.val :=
      Subtype.ext (phase_unchanged_nonrepresentative P.val Q.val active hrep)
    rw [he]
    exact ⟨0,Nat.zero_le _,MarkedRoute.nil _ (phase_good E P Q active)⟩
theorem prefix_marked_route (hn : 0<n) (k : ℕ) (hk : k ≤ n) :
    ∃ l ≤ k*(8*n*n+4), MarkedRoute Finset.univ (TrafficGood E P Q)
      (phaseState P Q 0) (phaseState P Q k) l := by
  induction k with
  | zero =>
    exact ⟨0,by simp,MarkedRoute.nil _ (phase_good E P Q ⟨0,hn⟩)⟩
  | succ k ih =>
    obtain ⟨a,ha,hra⟩ := ih (by omega)
    obtain ⟨b,hb,hrb⟩ := stage_marked_route E P Q ⟨k,by omega⟩
    exact ⟨a+b,by nlinarith,hra.append hrb⟩
theorem all_pairs_marked_route (hn : 0<n) :
    ∃ l ≤ n*(8*n*n+4), MarkedRoute Finset.univ (TrafficGood E P Q) P Q l := by
  have hp : phaseState P Q 0=P := Subtype.ext (phasePermutation_zero P.val Q.val)
  have hq : phaseState P Q n=Q := Subtype.ext (phasePermutation_full P.val Q.val)
  obtain ⟨l,hl,hr⟩ := prefix_marked_route E P Q hn n le_rfl
  exact ⟨l,hl,by simpa only [hp,hq] using hr⟩
end HiddenCircuits.Approximation.CanonicalPaths
