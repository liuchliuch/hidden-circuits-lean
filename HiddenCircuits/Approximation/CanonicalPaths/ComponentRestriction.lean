import HiddenCircuits.Approximation.CanonicalPaths.CycleEnumeration
import HiddenCircuits.Approximation.CanonicalPaths.CyclePresentation
import HiddenCircuits.Approximation.EndpointRestriction
import Mathlib.Data.Finset.Sort

/-! The literal sorted balanced submatrix belonging to one union component. -/
namespace HiddenCircuits.Approximation.CanonicalPaths.UnionReconstruction
open LocalRoutes
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (p q : Equiv.Perm (Fin n)) (active : Fin n)

@[simp] theorem mem_componentVertices (i : Fin n) :
    i∈componentVertices p q active ↔ (unionGraph p q).Reachable active i := by
  simp [componentVertices]

theorem card_componentVertices : (componentVertices p q active).card=componentPeriod p q active := by
  have he : Fintype.card {i // (unionGraph p q).Reachable active i}=componentPeriod p q active := by
    simpa using (Fintype.card_congr (orbitEquiv p q active)).symm
  simpa only [← mem_componentVertices, Fintype.card_coe] using he

noncomputable def componentRows : Finset (Fin n) := (componentVertices p q active).image p

theorem card_componentRows : (componentRows p q active).card=componentPeriod p q active := by
  rw [componentRows,Finset.card_image_of_injective _ p.injective,card_componentVertices]

noncomputable def columnOrder : Fin (componentPeriod p q active) ≃o componentVertices p q active :=
  (componentVertices p q active).orderIsoOfFin (card_componentVertices p q active)

noncomputable def rowOrder : Fin (componentPeriod p q active) ≃o componentRows p q active :=
  (componentRows p q active).orderIsoOfFin (card_componentRows p q active)

noncomputable def columns : Fin (componentPeriod p q active) ↪o Fin n :=
  (componentVertices p q active).orderEmbOfFin (card_componentVertices p q active)

noncomputable def rows : Fin (componentPeriod p q active) ↪o Fin n :=
  (componentRows p q active).orderEmbOfFin (card_componentRows p q active)

@[simp] theorem columnOrder_val (i : Fin (componentPeriod p q active)) :
    (columnOrder p q active i).val=columns p q active i := rfl
@[simp] theorem rowOrder_val (i : Fin (componentPeriod p q active)) :
    (rowOrder p q active i).val=rows p q active i := rfl

theorem columns_reachable (i : Fin (componentPeriod p q active)) :
    (unionGraph p q).Reachable active (columns p q active i) :=
  (mem_componentVertices p q active _).mp (columnOrder p q active i).property

theorem columns_range : Set.range (columns p q active)={i | (unionGraph p q).Reachable active i} := by
  ext i
  change (∃j,columns p q active j=i) ↔ _
  constructor
  · rintro ⟨j,rfl⟩
    exact columns_reachable p q active j
  · intro hi
    let x : componentVertices p q active := ⟨i,(mem_componentVertices p q active i).mpr hi⟩
    exact ⟨(columnOrder p q active).symm x,congrArg Subtype.val ((columnOrder p q active).apply_symm_apply x)⟩

theorem source_mem_rows (i : Fin (componentPeriod p q active)) :
    p (columns p q active i)∈componentRows p q active :=
  Finset.mem_image.mpr ⟨_,(columnOrder p q active i).property,rfl⟩

theorem target_mem_rows (i : Fin (componentPeriod p q active)) :
    q (columns p q active i)∈componentRows p q active := by
  refine Finset.mem_image.mpr ⟨relative p q (columns p q active i),?_,relative_apply p q _⟩
  exact (mem_componentVertices p q active _).mpr
    ((columns_reachable p q active i).trans (reachable_relative p q _))

noncomputable def restrictPermutation (f : Equiv.Perm (Fin n))
    (hf : ∀i,f (columns p q active i)∈componentRows p q active) :
    Equiv.Perm (Fin (componentPeriod p q active)) := by
  let g := fun i => (rowOrder p q active).symm ⟨f (columns p q active i),hf i⟩
  have hg : Function.Injective g := by
    intro a b h
    have he := congrArg (fun j => (rowOrder p q active j).val) h
    simp only [g,OrderIso.apply_symm_apply] at he
    exact (columns p q active).injective (f.injective he)
  exact Equiv.ofBijective g ⟨hg,Finite.surjective_of_injective hg⟩

theorem restrictPermutation_spec (f : Equiv.Perm (Fin n))
    (hf : ∀i,f (columns p q active i)∈componentRows p q active)
    (i : Fin (componentPeriod p q active)) :
    rows p q active (restrictPermutation p q active f hf i)=f (columns p q active i) := by
  change ((rowOrder p q active) ((rowOrder p q active).symm ⟨f (columns p q active i),hf i⟩)).val=_
  simp only [OrderIso.apply_symm_apply]

noncomputable def sourcePermutation := restrictPermutation p q active p (source_mem_rows p q active)
noncomputable def targetPermutation := restrictPermutation p q active q (target_mem_rows p q active)

@[simp] theorem sourcePermutation_spec (i : Fin (componentPeriod p q active)) :
    rows p q active (sourcePermutation p q active i)=p (columns p q active i) :=
  restrictPermutation_spec p q active p (source_mem_rows p q active) i
@[simp] theorem targetPermutation_spec (i : Fin (componentPeriod p q active)) :
    rows p q active (targetPermutation p q active i)=q (columns p q active i) :=
  restrictPermutation_spec p q active q (target_mem_rows p q active) i

noncomputable def restrictedEndpoints (E : MonotoneEndpoints n) :
    MonotoneEndpoints (componentPeriod p q active) :=
  E.restrict (rows p q active).toEmbedding (columns p q active).toEmbedding
    (rows p q active).strictMono (columns p q active).strictMono

theorem restricted_allowed (E : MonotoneEndpoints n) (i j : Fin (componentPeriod p q active)) :
    Allowed (restrictedEndpoints p q active E) i j ↔ Allowed E (rows p q active i) (columns p q active j) :=
  E.restrict_allowed _ _ _ _ i j

noncomputable def restrictedSource (E : MonotoneEndpoints n)
    (hp : ∀i,Allowed E (p i) i) : State (fun col row => Allowed (restrictedEndpoints p q active E) row col) :=
  ⟨sourcePermutation p q active,fun i => (restricted_allowed p q active E _ i).mpr (by
    rw [sourcePermutation_spec]; exact hp _)⟩
noncomputable def restrictedTarget (E : MonotoneEndpoints n)
    (hq : ∀i,Allowed E (q i) i) : State (fun col row => Allowed (restrictedEndpoints p q active E) row col) :=
  ⟨targetPermutation p q active,fun i => (restricted_allowed p q active E _ i).mpr (by
    rw [targetPermutation_spec]; exact hq _)⟩

noncomputable def cycleColumns : Equiv.Perm (Fin (componentPeriod p q active)) :=
  (orbitEquiv p q active).trans
    ((Equiv.subtypeEquivRight (fun i => (mem_componentVertices p q active i).symm)).trans
      (columnOrder p q active).toEquiv.symm)

@[simp] theorem cycleColumns_spec (i : Fin (componentPeriod p q active)) :
    columns p q active (cycleColumns p q active i)=orbitPoint p q active i := by
  change ((columnOrder p q active) ((columnOrder p q active).symm _)).val=_
  simp only [OrderIso.apply_symm_apply]
  rfl

noncomputable def componentPresentation (E : MonotoneEndpoints n)
    (hp : ∀i,Allowed E (p i) i) (hq : ∀i,Allowed E (q i) i) :
    CyclePresentation (restrictedEndpoints p q active E) where
  columns := cycleColumns p q active
  rows := (cycleColumns p q active).trans (sourcePermutation p q active)
  sourceEdges := by
    intro i
    apply (restricted_allowed p q active E _ _).mpr
    simp only [Equiv.trans_apply,sourcePermutation_spec]
    exact hp _
  targetEdges := by
    intro i
    apply (restricted_allowed p q active E _ _).mpr
    simp only [Equiv.trans_apply,sourcePermutation_spec,cycleColumns_spec,orbitPoint_rotate,relative_apply]
    exact hq _

end HiddenCircuits.Approximation.CanonicalPaths.UnionReconstruction
