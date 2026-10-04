import HiddenCircuits.DH.Decomposition

/-! Reindex the current representatives without changing any original graph bag. -/
namespace HiddenCircuits.DH.BoundaryPartition
universe u v w
variable {V : Type u} {R : Type v} {R' : Type w}
variable {G : SimpleGraph V} {H : SimpleGraph R} {H' : SimpleGraph R'}

def reindex (p : BoundaryPartition G H) (e : H ≃g H') : BoundaryPartition G H' where
  place a := e (p.place a)
  onto := e.toEquiv.surjective.comp p.onto
  active := p.active
  active_nonempty r := by
    obtain ⟨a,ha,haA⟩ := p.active_nonempty (e.symm r)
    exact ⟨a,by rw [ha,e.apply_symm_apply],haA⟩
  block a b hne := by
    have hn : p.place a≠p.place b := fun he => hne (congrArg e he)
    rw [p.block a b hn,e.map_rel_iff]

def reindexFiberEquiv (p : BoundaryPartition G H) (e : H ≃g H') (r : R') :
    p.Fiber (e.symm r) ≃ (p.reindex e).Fiber r where
  toFun a := ⟨a.val,by change e (p.place a.val)=r; rw [a.property,e.apply_symm_apply]⟩
  invFun a := ⟨a.val,by
    have h := congrArg e.symm a.property
    simpa only [reindex,e.symm_apply_apply] using h⟩
  left_inv _ := rfl
  right_inv _ := rfl

def reindexBagIso (p : BoundaryPartition G H) (e : H ≃g H') (r : R') :
    p.fiberGraph (e.symm r) ≃g (p.reindex e).fiberGraph r where
  toEquiv := p.reindexFiberEquiv e r
  map_rel_iff' := by rfl

lemma reindexBagIso_active (p : BoundaryPartition G H) (e : H ≃g H') (r : R') :
    p.reindexBagIso e r '' p.fiberActive (e.symm r) = (p.reindex e).fiberActive r := by
  ext a
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact hx
  · intro ha
    exact ⟨(p.reindexBagIso e r).symm a,ha,(p.reindexBagIso e r).apply_symm_apply a⟩

noncomputable def reindexRepresentation (p : BoundaryPartition G H) (rep : p.Representation)
    (e : H ≃g H') : (p.reindex e).Representation where
  expr r := rep.expr (e.symm r)
  iso r := (rep.iso (e.symm r)).trans (p.reindexBagIso e r)
  active_image r := by
    have hi := Set.image_image (p.reindexBagIso e r) (rep.iso (e.symm r)) (rep.expr (e.symm r)).active
    exact hi.symm.trans ((congrArg (Set.image (p.reindexBagIso e r))
      (rep.active_image (e.symm r))).trans (p.reindexBagIso_active e r))

end HiddenCircuits.DH.BoundaryPartition
