import HiddenCircuits.Approximation.CanonicalPaths.ComponentRestriction

/-! The orbit presentation has precisely the restricted original matchings. -/
namespace HiddenCircuits.Approximation.CanonicalPaths.UnionReconstruction
open LocalRoutes
variable {n : ℕ} (p q : Equiv.Perm (Fin n)) (active : Fin n)
  (E : MonotoneEndpoints n) (hp : ∀i,Allowed E (p i) i) (hq : ∀i,Allowed E (q i) i)

theorem componentPresentation_source :
    (componentPresentation p q active E hp hq).source=restrictedSource p q active E hp := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  simp [CyclePresentation.source,CyclePresentation.state,componentPresentation,restrictedSource]

theorem componentPresentation_target :
    (componentPresentation p q active E hp hq).target=restrictedTarget p q active E hq := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  obtain ⟨j,rfl⟩ := (cycleColumns p q active).surjective i
  apply (rows p q active).injective
  change rows p q active
    ((componentPresentation p q active E hp hq).target.val
      ((componentPresentation p q active E hp hq).columns j))=_
  rw [CyclePresentation.target,CyclePresentation.state_apply]
  change rows p q active (sourcePermutation p q active (cycleColumns p q active (finRotate _ j)))=
    rows p q active (targetPermutation p q active (cycleColumns p q active j))
  rw [sourcePermutation_spec,targetPermutation_spec,cycleColumns_spec,cycleColumns_spec,
    orbitPoint_rotate,relative_apply]

end HiddenCircuits.Approximation.CanonicalPaths.UnionReconstruction
