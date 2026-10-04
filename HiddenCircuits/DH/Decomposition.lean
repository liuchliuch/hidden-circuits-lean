import HiddenCircuits.DH.BagIteration
import HiddenCircuits.DH.ExecutionBits

/-! Conversion of graph-semantic pruning operations to the verified executable bag forest.
A pruning sequence remains an explicit hypothesis until the ordinary-input preprocessing proof. -/
namespace HiddenCircuits.DH
universe u v w x
variable {V : Type u} {W : Type v} {V' : Type w} {W' : Type x}
variable {G : SimpleGraph V} {H : SimpleGraph W} {G' : SimpleGraph V'} {H' : SimpleGraph W'}

lemma iso_mem_image (e : G ≃g G') (T : Set V) (a : V) : e a ∈ e '' T ↔ a ∈ T := by
  constructor
  · rintro ⟨b,hb,he⟩
    exact e.injective he ▸ hb
  · intro ha
    exact ⟨a,ha,rfl⟩

def disjointCongrIso (e : G ≃g G') (f : H ≃g H') :
    disjointGraph G H ≃g disjointGraph G' H' where
  toEquiv := e.toEquiv.sumCongr f.toEquiv
  map_rel_iff' := by
    rintro (a | a) (b | b)
    · exact e.map_rel_iff
    · rfl
    · rfl
    · exact f.map_rel_iff

def joinCongrIso (e : G ≃g G') (f : H ≃g H') (T : Set V) (U : Set W) :
    joinGraph G H T U ≃g joinGraph G' H' (e '' T) (f '' U) where
  toEquiv := e.toEquiv.sumCongr f.toEquiv
  map_rel_iff' := by
    rintro (a | a) (b | b)
    · exact e.map_rel_iff
    · change (e a ∈ e '' T ∧ f b ∈ f '' U) ↔ a ∈ T ∧ b ∈ U
      rw [iso_mem_image,iso_mem_image]
    · change (e b ∈ e '' T ∧ f a ∈ f '' U) ↔ b ∈ T ∧ a ∈ U
      rw [iso_mem_image,iso_mem_image]
    · exact f.map_rel_iff

lemma sumCongr_twin_active (e : V ≃ V') (f : W ≃ W') (T : Set V) (U : Set W) :
    (e.sumCongr f) '' {a | Sum.elim T U a} = {a | Sum.elim (e '' T) (f '' U) a} := by
  ext a
  cases a <;> simp [Set.mem_image,Sum.exists] <;> rfl

lemma sumCongr_pendant_active (e : V ≃ V') (f : W ≃ W') (T : Set V) :
    (e.sumCongr f) '' {a | ∃ t ∈ T, a = Sum.inl t} =
      {a | ∃ t ∈ e '' T, a = Sum.inl t} := by
  have hm (a : V') : (∃ b ∈ T, e b = a) ↔ e.symm a ∈ T := by
    constructor
    · rintro ⟨b,hb,he⟩
      have hb' : b = e.symm a := e.eq_symm_apply.mpr he
      exact hb' ▸ hb
    · intro ha
      exact ⟨e.symm a,ha,e.apply_symm_apply a⟩
  ext a
  cases a <;> simp [Set.mem_image,Sum.exists,hm]

namespace BoundaryPartition
variable {R : Type v} {K : SimpleGraph R}

/-- Each semantic original-vertex bag is represented by an actual executable bag expression. -/
structure Representation (p : BoundaryPartition G K) where
  expr : R → BagExpr
  iso : ∀ r, (expr r).graph ≃g p.fiberGraph r
  active_image : ∀ r, iso r '' (expr r).active = p.fiberActive r

noncomputable def initialRepresentation (G : SimpleGraph V) : (initial G).Representation where
  expr _ := .leaf
  iso r := (initialFiberIso G r).symm
  active_image r := by
    change (initialFiberIso G r).symm '' Set.univ = Set.univ
    ext a
    constructor
    · intro _; trivial
    · intro _
      obtain ⟨b,rfl⟩ := (initialFiberIso G r).symm.toEquiv.surjective a
      exact ⟨b,Set.mem_univ _,rfl⟩

/-- Finalizing another representative only removes an outer subtype wrapper from an unaffected bag. -/
def finalizeFiberEquiv (p : BoundaryPartition G K) (u : R) (r : {r : R // r ≠ u}) :
    p.Fiber r.val ≃ (p.finalize u).Fiber r where
  toFun a := ⟨⟨a.val,by rw [a.property]; exact r.property⟩,Subtype.ext a.property⟩
  invFun a := ⟨a.val.val,congrArg Subtype.val a.property⟩
  left_inv a := rfl
  right_inv a := rfl

def finalizeBagIso (p : BoundaryPartition G K) (u : R) (r : {r : R // r ≠ u}) :
    p.fiberGraph r.val ≃g (p.finalize u).fiberGraph r where
  toEquiv := p.finalizeFiberEquiv u r
  map_rel_iff' := by rfl

lemma finalize_active_image (p : BoundaryPartition G K) (u : R) (r : {r : R // r ≠ u}) :
    p.finalizeBagIso u r '' p.fiberActive r.val = (p.finalize u).fiberActive r := by
  ext a
  constructor
  · rintro ⟨b,hb,rfl⟩
    exact hb
  · intro ha
    exact ⟨(p.finalizeFiberEquiv u r).symm a,ha,rfl⟩

noncomputable def Representation.finalize {p : BoundaryPartition G K}
    (rep : p.Representation) (u : R) : (p.finalize u).Representation where
  expr r := rep.expr r.val
  iso r := (rep.iso r.val).trans (p.finalizeBagIso u r)
  active_image r := by
    change (fun a => p.finalizeBagIso u r (rep.iso r.val a)) '' _ = _
    rw [← Set.image_image,rep.active_image,p.finalize_active_image]

/-- The concrete expression-table update uses only a label comparison and one constructor. -/
def updateExpr [DecidableEq R] (es : R → BagExpr) (u v : R)
    (combine : BagExpr → BagExpr → BagExpr) (r : {r : R // r ≠ v}) : BagExpr :=
  if r.val = u then combine (es u) (es v) else es r.val

namespace Representation
variable {p : BoundaryPartition G K} (rep : p.Representation)

noncomputable def joinedIso (u v : R) :
    joinGraph (rep.expr u).graph (rep.expr v).graph (rep.expr u).active (rep.expr v).active ≃g
      joinGraph (p.fiberGraph u) (p.fiberGraph v) (p.fiberActive u) (p.fiberActive v) where
  toEquiv := (rep.iso u).toEquiv.sumCongr (rep.iso v).toEquiv
  map_rel_iff' := by
    rintro (a | a) (b | b)
    · exact (rep.iso u).map_rel_iff
    · change (rep.iso u a ∈ p.fiberActive u ∧ rep.iso v b ∈ p.fiberActive v) ↔ _
      rw [← rep.active_image u,← rep.active_image v,iso_mem_image,iso_mem_image]
      rfl
    · change (rep.iso u b ∈ p.fiberActive u ∧ rep.iso v a ∈ p.fiberActive v) ↔ _
      rw [← rep.active_image u,← rep.active_image v,iso_mem_image,iso_mem_image]
      rfl
    · exact (rep.iso v).map_rel_iff

lemma sum_active_twin (u v : R) :
    ((rep.iso u).toEquiv.sumCongr (rep.iso v).toEquiv) ''
      {a | Sum.elim (rep.expr u).active (rep.expr v).active a} =
      {a | Sum.elim (p.fiberActive u) (p.fiberActive v) a} := by
  rw [sumCongr_twin_active]
  change {a | Sum.elim (rep.iso u '' (rep.expr u).active) (rep.iso v '' (rep.expr v).active) a} = _
  rw [rep.active_image,rep.active_image]

lemma sum_active_pendant (u v : R) :
    ((rep.iso u).toEquiv.sumCongr (rep.iso v).toEquiv) ''
      {a | ∃ t ∈ (rep.expr u).active, a = Sum.inl t} =
      {a | ∃ t ∈ p.fiberActive u, a = Sum.inl t} := by
  rw [sumCongr_pendant_active]
  change {a | ∃ t ∈ (rep.iso u '' (rep.expr u).active), a = Sum.inl t} = _
  rw [rep.active_image]

noncomputable def trueTwinMergedIso {u v : R} (ht : TwinPair K u v) (ha : K.Adj u v) :
    (BagExpr.trueTwin (rep.expr u) (rep.expr v)).graph ≃g
      (p.twinMerge ht).fiberGraph ⟨u,ht.distinct⟩ :=
  (rep.joinedIso u v).trans (p.joinBagIso u v ht.distinct ha)

lemma trueTwinMergedIso_active {u v : R} (ht : TwinPair K u v) (ha : K.Adj u v) :
    rep.trueTwinMergedIso ht ha '' (BagExpr.trueTwin (rep.expr u) (rep.expr v)).active =
      (p.twinMerge ht).fiberActive ⟨u,ht.distinct⟩ := by
  change (fun a => p.joinBagIso u v ht.distinct ha (rep.joinedIso u v a)) '' _ = _
  rw [← Set.image_image]
  change (p.mergeFiberEquiv u v ht.distinct).symm ''
    (((rep.iso u).toEquiv.sumCongr (rep.iso v).toEquiv) '' _) = _
  exact (congrArg (Set.image (p.mergeFiberEquiv u v ht.distinct).symm)
    (rep.sum_active_twin u v)).trans (p.mergeFiberEquiv_twin_active u v ht.distinct)

noncomputable def falseTwinMergedIso {u v : R} (ht : TwinPair K u v) (ha : ¬K.Adj u v) :
    (BagExpr.falseTwin (rep.expr u) (rep.expr v)).graph ≃g
      (p.twinMerge ht).fiberGraph ⟨u,ht.distinct⟩ :=
  (disjointCongrIso (rep.iso u) (rep.iso v)).trans (p.disjointBagIso u v ht.distinct ha)

lemma falseTwinMergedIso_active {u v : R} (ht : TwinPair K u v) (ha : ¬K.Adj u v) :
    rep.falseTwinMergedIso ht ha '' (BagExpr.falseTwin (rep.expr u) (rep.expr v)).active =
      (p.twinMerge ht).fiberActive ⟨u,ht.distinct⟩ := by
  change (fun a => p.disjointBagIso u v ht.distinct ha (disjointCongrIso (rep.iso u) (rep.iso v) a)) '' _ = _
  rw [← Set.image_image]
  change (p.mergeFiberEquiv u v ht.distinct).symm ''
    (((rep.iso u).toEquiv.sumCongr (rep.iso v).toEquiv) '' _) = _
  exact (congrArg (Set.image (p.mergeFiberEquiv u v ht.distinct).symm)
    (rep.sum_active_twin u v)).trans (p.mergeFiberEquiv_twin_active u v ht.distinct)

noncomputable def pendantMergedIso {u v : R} (hp : PendantPair K u v) :
    (BagExpr.pendant (rep.expr u) (rep.expr v)).graph ≃g
      (p.pendantMerge hp).fiberGraph ⟨u,hp.distinct⟩ :=
  (rep.joinedIso u v).trans (p.joinBagIso u v hp.distinct hp.adjacent.symm)

lemma pendantMergedIso_active {u v : R} (hp : PendantPair K u v) :
    rep.pendantMergedIso hp '' (BagExpr.pendant (rep.expr u) (rep.expr v)).active =
      (p.pendantMerge hp).fiberActive ⟨u,hp.distinct⟩ := by
  change (fun a => p.joinBagIso u v hp.distinct hp.adjacent.symm (rep.joinedIso u v a)) '' _ = _
  rw [← Set.image_image]
  change (p.mergeFiberEquiv u v hp.distinct).symm ''
    (((rep.iso u).toEquiv.sumCongr (rep.iso v).toEquiv) '' _) = _
  exact (congrArg (Set.image (p.mergeFiberEquiv u v hp.distinct).symm)
    (rep.sum_active_pendant u v)).trans (p.mergeFiberEquiv_pendant_active u v hp.distinct)

noncomputable def twinOtherIso {u v : R} (ht : TwinPair K u v)
    (r : {r : R // r ≠ v}) (hr : r.val ≠ u) :
    (rep.expr r.val).graph ≃g (p.twinMerge ht).fiberGraph r :=
  (rep.iso r.val).trans (p.otherBagIso u v ht.distinct r hr)

lemma twinOtherIso_active {u v : R} (ht : TwinPair K u v)
    (r : {r : R // r ≠ v}) (hr : r.val ≠ u) :
    rep.twinOtherIso ht r hr '' (rep.expr r.val).active = (p.twinMerge ht).fiberActive r := by
  change (fun a => p.otherBagIso u v ht.distinct r hr (rep.iso r.val a)) '' _ = _
  rw [← Set.image_image,rep.active_image]
  change p.otherFiberEquiv u v ht.distinct r hr '' _ = _
  rw [p.otherFiberEquiv_twin_active]
  rfl

noncomputable def pendantOtherIso {u v : R} (hp : PendantPair K u v)
    (r : {r : R // r ≠ v}) (hr : r.val ≠ u) :
    (rep.expr r.val).graph ≃g (p.pendantMerge hp).fiberGraph r :=
  (rep.iso r.val).trans (p.otherBagIso u v hp.distinct r hr)

lemma pendantOtherIso_active {u v : R} (hp : PendantPair K u v)
    (r : {r : R // r ≠ v}) (hr : r.val ≠ u) :
    rep.pendantOtherIso hp r hr '' (rep.expr r.val).active = (p.pendantMerge hp).fiberActive r := by
  change (fun a => p.otherBagIso u v hp.distinct r hr (rep.iso r.val a)) '' _ = _
  rw [← Set.image_image,rep.active_image]
  change p.otherFiberEquiv u v hp.distinct r hr '' _ = _
  rw [p.otherFiberEquiv_pendant_active]
  rfl

/-- Assemble the updated expression table from the proved merged and unchanged induced-bag isos. -/
noncomputable def update [DecidableEq R] {u v : R} (huv : u ≠ v)
    (p' : BoundaryPartition G (K.induce {r : R | r ≠ v}))
    (combine : BagExpr → BagExpr → BagExpr)
    (merged : (combine (rep.expr u) (rep.expr v)).graph ≃g p'.fiberGraph ⟨u,huv⟩)
    (merged_active : merged '' (combine (rep.expr u) (rep.expr v)).active = p'.fiberActive ⟨u,huv⟩)
    (other : ∀ r : {r : R // r ≠ v}, r.val ≠ u →
      (rep.expr r.val).graph ≃g p'.fiberGraph r)
    (other_active : ∀ (r : {r : R // r ≠ v}) (hr : r.val ≠ u),
      other r hr '' (rep.expr r.val).active = p'.fiberActive r) : p'.Representation := by
  let bundle (r : {r : R // r ≠ v}) :
      Σ e : BagExpr, {f : e.graph ≃g p'.fiberGraph r // f '' e.active = p'.fiberActive r} := by
    by_cases hr : r.val = u
    · rcases r with ⟨r,hrv⟩
      dsimp only at hr
      subst r
      exact ⟨combine (rep.expr u) (rep.expr v),merged,merged_active⟩
    · exact ⟨rep.expr r.val,other r hr,other_active r hr⟩
  exact ⟨fun r => (bundle r).1,fun r => (bundle r).2.val,fun r => (bundle r).2.property⟩

noncomputable def trueTwin [DecidableEq R] {u v : R} (ht : TwinPair K u v) (ha : K.Adj u v) :
    (p.twinMerge ht).Representation :=
  rep.update ht.distinct (p.twinMerge ht) BagExpr.trueTwin
    (rep.trueTwinMergedIso ht ha) (rep.trueTwinMergedIso_active ht ha)
    (rep.twinOtherIso ht) (rep.twinOtherIso_active ht)

noncomputable def falseTwin [DecidableEq R] {u v : R} (ht : TwinPair K u v) (ha : ¬K.Adj u v) :
    (p.twinMerge ht).Representation :=
  rep.update ht.distinct (p.twinMerge ht) BagExpr.falseTwin
    (rep.falseTwinMergedIso ht ha) (rep.falseTwinMergedIso_active ht ha)
    (rep.twinOtherIso ht) (rep.twinOtherIso_active ht)

noncomputable def pendant [DecidableEq R] {u v : R} (hp : PendantPair K u v) :
    (p.pendantMerge hp).Representation :=
  rep.update hp.distinct (p.pendantMerge hp) BagExpr.pendant
    (rep.pendantMergedIso hp) (rep.pendantMergedIso_active hp)
    (rep.pendantOtherIso hp) (rep.pendantOtherIso_active hp)

@[simp] lemma trueTwin_expr [DecidableEq R] {u v : R} (ht : TwinPair K u v) (ha : K.Adj u v) :
    (rep.trueTwin ht ha).expr = updateExpr rep.expr u v BagExpr.trueTwin := by
  funext r
  by_cases hr : r.val = u
  · rcases r with ⟨r,hrv⟩
    dsimp only at hr
    subst r
    simp [trueTwin,update,updateExpr]
  · simp [trueTwin,update,updateExpr,hr]

@[simp] lemma falseTwin_expr [DecidableEq R] {u v : R} (ht : TwinPair K u v) (ha : ¬K.Adj u v) :
    (rep.falseTwin ht ha).expr = updateExpr rep.expr u v BagExpr.falseTwin := by
  funext r
  by_cases hr : r.val = u
  · rcases r with ⟨r,hrv⟩
    dsimp only at hr
    subst r
    simp [falseTwin,update,updateExpr]
  · simp [falseTwin,update,updateExpr,hr]

@[simp] lemma pendant_expr [DecidableEq R] {u v : R} (hp : PendantPair K u v) :
    (rep.pendant hp).expr = updateExpr rep.expr u v BagExpr.pendant := by
  funext r
  by_cases hr : r.val = u
  · rcases r with ⟨r,hrv⟩
    dsimp only at hr
    subst r
    simp [pendant,update,updateExpr]
  · simp [pendant,update,updateExpr,hr]

end Representation

end BoundaryPartition
/-- A graph-semantic pruning trace. Every deletion records the actual adjacency condition. -/
inductive PruneSequence : {R : Type v} → SimpleGraph R → Type (v+1) where
  | done {R : Type v} {H : SimpleGraph R} (empty : IsEmpty R) : PruneSequence H
  | isolated {R : Type v} {H : SimpleGraph R} (u : R) (hu : ∀ r, ¬H.Adj u r)
      (next : PruneSequence (H.induce {r | r ≠ u})) : PruneSequence H
  | falseTwin {R : Type v} {H : SimpleGraph R} (u v : R) (ht : TwinPair H u v)
      (ha : ¬H.Adj u v) (next : PruneSequence (H.induce {r | r ≠ v})) : PruneSequence H
  | trueTwin {R : Type v} {H : SimpleGraph R} (u v : R) (ht : TwinPair H u v)
      (ha : H.Adj u v) (next : PruneSequence (H.induce {r | r ≠ v})) : PruneSequence H
  | pendant {R : Type v} {H : SimpleGraph R} (u v : R) (hp : PendantPair H u v)
      (next : PruneSequence (H.induce {r | r ≠ v})) : PruneSequence H

namespace PruneSequence
open BoundaryPartition

/-- Executable expression-table processing of the deletion sequence. -/
def toForest {R : Type v} [DecidableEq R] {H : SimpleGraph R}
    (s : PruneSequence H) (es : R → BagExpr) : List BagExpr :=
  match s with
  | .done _ => []
  | .isolated u _ next => es u :: next.toForest (fun r => es r.val)
  | .falseTwin u v _ _ next => next.toForest (updateExpr es u v BagExpr.falseTwin)
  | .trueTwin u v _ _ next => next.toForest (updateExpr es u v BagExpr.trueTwin)
  | .pendant u v _ next => next.toForest (updateExpr es u v BagExpr.pendant)

/-- The graph represented by the accumulated expression forest is the unchanged original graph. -/
noncomputable def toForestIso {R : Type v} [DecidableEq R] {H : SimpleGraph R}
    (s : PruneSequence H) {V : Type u} {G : SimpleGraph V}
    (p : BoundaryPartition G H) (rep : p.Representation) :
    BagForest.graph (s.toForest rep.expr) ≃g G := by
  cases s with
  | done he =>
    haveI : IsEmpty V := ⟨fun a => he.false (p.place a)⟩
    refine ⟨(Equiv.equivEmpty V).symm,?_⟩
    intro a
    cases a
  | isolated u hu next =>
    exact (disjointCongrIso (rep.iso u)
      (next.toForestIso (p.finalize u) (rep.finalize u))).trans (p.isolatedBagIso u hu)
  | falseTwin u v ht ha next =>
    have ih := next.toForestIso (p.twinMerge ht) (rep.falseTwin ht ha)
    rw [rep.falseTwin_expr ht ha] at ih
    exact ih
  | trueTwin u v ht ha next =>
    have ih := next.toForestIso (p.twinMerge ht) (rep.trueTwin ht ha)
    rw [rep.trueTwin_expr ht ha] at ih
    exact ih
  | pendant u v hp next =>
    have ih := next.toForestIso (p.pendantMerge hp) (rep.pendant hp)
    rw [rep.pendant_expr hp] at ih
    exact ih

/-- Start the executable expression table with the singleton bag at each original vertex. -/
def forest {R : Type v} [DecidableEq R] {H : SimpleGraph R} (s : PruneSequence H) : List BagExpr :=
  s.toForest (fun _ => BagExpr.leaf)

noncomputable def forestIso {R : Type v} [DecidableEq R] {H : SimpleGraph R} (s : PruneSequence H) :
    BagForest.graph s.forest ≃g H :=
  s.toForestIso (BoundaryPartition.initial H) (BoundaryPartition.initialRepresentation H)

/-- A semantic pruning sequence now suffices; no graph-forest isomorphism certificate is supplied. -/
theorem execute_spec {R : Type v} [Fintype R] [DecidableEq R] {H : SimpleGraph R}
    (s : PruneSequence H) :
    (BagForest.execute s.forest).value = (perfectMatchingCount H : ℤ) ∧
    (BagForest.execute s.forest).operations ≤ 36*(Fintype.card R).choose 2+Fintype.card R ∧
    ExecutionBits.ForestProperty (fun z => z.natAbs.size ≤
      (3*Fintype.card R+3)*(Fintype.card R+1).size+2) s.forest :=
  ExecutionBits.complete_execution_bit_spec_of_iso s.forest H s.forestIso

end PruneSequence

end HiddenCircuits.DH
