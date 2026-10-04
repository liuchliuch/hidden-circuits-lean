import HiddenCircuits.Approximation.CanonicalPaths.ComponentCorrespondence
import HiddenCircuits.Approximation.CanonicalPaths.LiftedCompanions

/-! Actual component replacements inside complementary global phases. -/
namespace HiddenCircuits.Approximation.CanonicalPaths.UnionReconstruction
open LocalRoutes
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (E : MonotoneEndpoints n)
  (P Q : State (fun col row => Allowed E row col)) (active : Fin n)
  (hrep : componentMin P.val Q.val active=active)
include hrep

private theorem component_base (i : Fin (componentPeriod P.val Q.val active)) :
    (phaseState P Q active.val).val (columns P.val Q.val active i)=
      rows P.val Q.val active (sourcePermutation P.val Q.val active i) := by
  rw [sourcePermutation_spec]
  exact phase_before_component P.val Q.val active _ hrep (columns_reachable _ _ _ _)

private theorem complementary_base (i : Fin (componentPeriod P.val Q.val active)) :
    (phaseState Q P active.val).val (columns P.val Q.val active i)=
      rows P.val Q.val active (targetPermutation P.val Q.val active i) := by
  rw [targetPermutation_spec]
  exact phase_before_component Q.val P.val active _
    (by rw [componentMin_swap]; exact hrep)
    (by rw [unionGraph_swap]; exact columns_reachable _ _ _ _)

noncomputable def liftComponentState
    (z : State (fun col row => Allowed (restrictedEndpoints P.val Q.val active E) row col)) :
    State (fun col row => Allowed E row col) :=
  liftState (columns P.val Q.val active).toEmbedding (rows P.val Q.val active)
    (phaseState P Q active.val) (sourcePermutation P.val Q.val active)
    (component_base E P Q active hrep)
    (fun i j h => (restricted_allowed P.val Q.val active E j i).mp h) z

noncomputable def liftComplementState
    (z : State (fun col row => Allowed (restrictedEndpoints P.val Q.val active E) row col)) :
    State (fun col row => Allowed E row col) :=
  liftState (columns P.val Q.val active).toEmbedding (rows P.val Q.val active)
    (phaseState Q P active.val) (targetPermutation P.val Q.val active)
    (complementary_base E P Q active hrep)
    (fun i j h => (restricted_allowed P.val Q.val active E j i).mp h) z

@[simp] theorem liftComponentState_column
    (z : State (fun col row => Allowed (restrictedEndpoints P.val Q.val active E) row col))
    (i : Fin (componentPeriod P.val Q.val active)) :
    (liftComponentState E P Q active hrep z).val (columns P.val Q.val active i)=rows P.val Q.val active (z.val i) :=
  liftState_column _ _ _ _ _ _ _ _

@[simp] theorem liftComplementState_column
    (z : State (fun col row => Allowed (restrictedEndpoints P.val Q.val active E) row col))
    (i : Fin (componentPeriod P.val Q.val active)) :
    (liftComplementState E P Q active hrep z).val (columns P.val Q.val active i)=rows P.val Q.val active (z.val i) :=
  liftState_column _ _ _ _ _ _ _ _

theorem liftComponentState_outside
    (z : State (fun col row => Allowed (restrictedEndpoints P.val Q.val active E) row col))
    (i : Fin n) (hi : ¬(unionGraph P.val Q.val).Reachable active i) :
    (liftComponentState E P Q active hrep z).val i=(phaseState P Q active.val).val i := by
  apply liftState_outside
  change i∉Set.range (columns P.val Q.val active)
  rw [columns_range]
  exact hi

theorem liftComplementState_outside
    (z : State (fun col row => Allowed (restrictedEndpoints P.val Q.val active E) row col))
    (i : Fin n) (hi : ¬(unionGraph P.val Q.val).Reachable active i) :
    (liftComplementState E P Q active hrep z).val i=(phaseState Q P active.val).val i := by
  apply liftState_outside
  change i∉Set.range (columns P.val Q.val active)
  rw [columns_range]
  exact hi

@[simp] theorem liftComponentState_source :
    liftComponentState E P Q active hrep (restrictedSource P.val Q.val active E P.property)=
      phaseState P Q active.val := by
  apply Subtype.ext
  exact liftPermutation_source _ _ _

@[simp] theorem liftComponentState_target :
    liftComponentState E P Q active hrep (restrictedTarget P.val Q.val active E Q.property)=
      phaseState P Q (active.val+1) := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  by_cases hi : (unionGraph P.val Q.val).Reachable active i
  · have hir : i∈Set.range (columns P.val Q.val active) := by
      rw [columns_range]
      exact hi
    obtain ⟨j,rfl⟩ := hir
    rw [liftComponentState_column]
    change rows P.val Q.val active (targetPermutation P.val Q.val active j)=_
    rw [targetPermutation_spec]
    exact (phase_after_component P.val Q.val active _ hrep hi).symm
  · rw [liftComponentState_outside E P Q active hrep _ i hi]
    exact (phase_unchanged_outside P.val Q.val active i hi).symm

theorem liftComponentState_companion
    {z : State (fun col row => Allowed (restrictedEndpoints P.val Q.val active E) row col)}
    {d : ℕ} (hz : HasCompanion (restrictedSource P.val Q.val active E P.property)
      (restrictedTarget P.val Q.val active E Q.property) z d) :
    HasCompanion P Q (liftComponentState E P Q active hrep z) d := by
  apply HasCompanion.lift (columns P.val Q.val active).toEmbedding (rows P.val Q.val active)
    (restrictedSource P.val Q.val active E P.property)
    (restrictedTarget P.val Q.val active E Q.property) P Q
    (liftComponentState E P Q active hrep) (liftComplementState E P Q active hrep)
    (liftComponentState_column E P Q active hrep) (liftComplementState_column E P Q active hrep)
    (fun i => (sourcePermutation_spec _ _ _ i).symm)
    (fun i => (targetPermutation_spec _ _ _ i).symm) _ hz
  intro z w i hi
  have hin : ¬(unionGraph P.val Q.val).Reachable active i := by
    change i∉Set.range (columns P.val Q.val active) at hi
    rw [columns_range] at hi
    exact hi
  rw [liftComponentState_outside E P Q active hrep _ _ hin,
    liftComplementState_outside E P Q active hrep _ _ hin]
  exact phase_complement P.val Q.val active.val i

theorem liftComponentState_interrupted
    (z : State (fun col row => Allowed (restrictedEndpoints P.val Q.val active E) row col)) :
    Interrupted P.val Q.val (liftComponentState E P Q active hrep z).val active :=
  liftComponentState_outside E P Q active hrep z

theorem component_stage_of_route {l : ℕ}
    (route : MarkedRoute Finset.univ
      (fun z => HasCompanion (restrictedSource P.val Q.val active E P.property)
        (restrictedTarget P.val Q.val active E Q.property) z 6)
      (restrictedSource P.val Q.val active E P.property)
      (restrictedTarget P.val Q.val active E Q.property) l) :
    MarkedRoute Finset.univ
      (fun z => HasCompanion P Q z 6 ∧ Interrupted P.val Q.val z.val active)
      (phaseState P Q active.val) (phaseState P Q (active.val+1)) l := by
  have h := route.map (liftComponentState E P Q active hrep)
    (Good' := fun z => HasCompanion P Q z 6 ∧ Interrupted P.val Q.val z.val active)
    (fun _ _ hm => liftState_move _ _ _ _ _ _ hm)
    (fun z hz => ⟨liftComponentState_companion E P Q active hrep hz,
      liftComponentState_interrupted E P Q active hrep z⟩)
  simpa only [liftComponentState_source,liftComponentState_target] using h

end HiddenCircuits.Approximation.CanonicalPaths.UnionReconstruction
