import HiddenCircuits.PerfectPartners
namespace HiddenCircuits.Approximation
attribute [local instance] Classical.propDecidable
open scoped BigOperators
def withoutPair {V : Type*} (u v : V) : Set V := {x | x≠u ∧ x≠v}
abbrev EdgeFiber {V : Type*} (G : SimpleGraph V) (u v : V) :=
  {p : PerfectPartner G // p.val u=v}
namespace EdgeFiber
variable {V : Type*} {G : SimpleGraph V} {u v : V}
theorem partner_back (p : EdgeFiber G u v) : p.val.val v=u := by
  exact (congrArg p.val.val p.property).symm.trans (p.val.property.1 u)
def restrict (p : EdgeFiber G u v) : PerfectPartner (G.induce (withoutPair u v)) := by
  let f : withoutPair u v → withoutPair u v := fun x =>
    ⟨p.val.val x.val,by
      constructor
      · intro h
        have hh := congrArg p.val.val h
        rw [p.val.property.1 x.val,p.property] at hh
        exact x.property.2 hh
      · intro h
        have hh := congrArg p.val.val h
        rw [p.val.property.1 x.val,p.partner_back] at hh
        exact x.property.1 hh⟩
  refine ⟨f,?_,?_⟩
  · intro x
    exact Subtype.ext (p.val.property.1 x.val)
  · intro x
    exact p.val.property.2 x.val
end EdgeFiber
namespace InsertEdge
variable {V : Type*} {G : SimpleGraph V} {u v : V}
noncomputable def partner (q : PerfectPartner (G.induce (withoutPair u v))) (x : V) : V :=
  if hx : x=u then v else if hy : x=v then u else
    (q.val ⟨x,hx,hy⟩).val
@[simp] theorem partner_left (q : PerfectPartner (G.induce (withoutPair u v))) :
    partner q u=v := by simp [partner]
@[simp] theorem partner_right (q : PerfectPartner (G.induce (withoutPair u v))) (hne : u≠v) :
    partner q v=u := by simp [partner,hne.symm]
theorem partner_retained (q : PerfectPartner (G.induce (withoutPair u v)))
    (x : withoutPair u v) : partner q x.val=(q.val x).val := by
  simp [partner,x.property.1,x.property.2]
noncomputable def extend (huv : G.Adj u v) (q : PerfectPartner (G.induce (withoutPair u v))) :
    EdgeFiber G u v := by
  have hne : u≠v := huv.ne
  refine ⟨⟨partner q,?_,?_⟩,partner_left q⟩
  · intro x
    by_cases hxu : x=u
    · subst x
      simp [hne]
    by_cases hxv : x=v
    · subst x
      simp [hne]
    let z : withoutPair u v := ⟨x,hxu,hxv⟩
    change partner q (partner q z.val)=z.val
    rw [partner_retained q z,partner_retained q (q.val z),q.property.1 z]
  · intro x
    by_cases hxu : x=u
    · subst x
      simpa using huv
    by_cases hxv : x=v
    · subst x
      simpa [hne] using huv.symm
    let z : withoutPair u v := ⟨x,hxu,hxv⟩
    change G.Adj z.val (partner q z.val)
    rw [partner_retained]
    exact q.property.2 z
theorem restrict_extend (huv : G.Adj u v) (q : PerfectPartner (G.induce (withoutPair u v))) :
    (extend huv q).restrict=q := by
  apply Subtype.ext
  funext x
  apply Subtype.ext
  exact partner_retained q x
theorem extend_restrict (huv : G.Adj u v) (p : EdgeFiber G u v) :
    extend huv p.restrict=p := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change partner p.restrict x=p.val.val x
  by_cases hxu : x=u
  · subst x
    simpa using p.property.symm
  by_cases hxv : x=v
  · subst x
    simpa [huv.ne] using p.partner_back.symm
  exact partner_retained p.restrict ⟨x,hxu,hxv⟩
end InsertEdge
noncomputable def edgeDeletionEquiv {V : Type*} {G : SimpleGraph V} {u v : V}
    (huv : G.Adj u v) : EdgeFiber G u v ≃ PerfectPartner (G.induce (withoutPair u v)) where
  toFun := EdgeFiber.restrict
  invFun := InsertEdge.extend huv
  left_inv := InsertEdge.extend_restrict huv
  right_inv := InsertEdge.restrict_extend huv
noncomputable def partnerFiberEquiv {V : Type*} (G : SimpleGraph V) (u : V) :
    PerfectPartner G ≃ Σ v : {v // G.Adj u v}, EdgeFiber G u v.val where
  toFun p := ⟨⟨p.val u,p.property.2 u⟩,⟨p,rfl⟩⟩
  invFun q := q.2.val
  left_inv p := rfl
  right_inv q := by
    rcases q with ⟨⟨v,hv⟩,⟨p,hp⟩⟩
    dsimp
    cases hp
    rfl
theorem perfectMatchingCount_delete_pair {V : Type*} [Fintype V]
    (G : SimpleGraph V) (u : V) :
    perfectMatchingCount G =
      ∑ v : {v // G.Adj u v}, perfectMatchingCount (G.induce (withoutPair u v.val)) := by
  classical
  rw [perfectMatchingCount_eq_partners,Fintype.card_congr (partnerFiberEquiv G u),Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro v _
  rw [perfectMatchingCount_eq_partners]
  exact Fintype.card_congr (edgeDeletionEquiv v.property)
end HiddenCircuits.Approximation
