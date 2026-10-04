import HiddenCircuits.Approximation.CanonicalPaths.MountainReplacement

/-! Fresh event-incidence pairing, derived from local replacements and uniqueness. -/
namespace HiddenCircuits.Approximation.CanonicalPaths.MountainSystem
variable {E F : Type*} {H : ℕ} (A : Side E H) (B : Side F H)

def LeftMove (p q : Port A B) : Prop := ∃u,
  portHeight A B p=A.height p.1.val.1 u ∧ q.1.val.1=(A.mate (p.1.val.1,u)).1 ∧
  q.1.val.2=p.1.val.2 ∧ portHeight A B q=portHeight A B p

def RightMove (p q : Port A B) : Prop := ∃u,
  portHeight A B p=B.height p.1.val.2 u ∧ q.1.val.1=p.1.val.1 ∧
  q.1.val.2=(B.mate (p.1.val.2,u)).1 ∧ portHeight A B q=portHeight A B p

def Incidence (p q : Port A B) : Prop := LeftMove A B p q ∨ RightMove A B p q

theorem LeftMove.symm {p q : Port A B} (h : LeftMove A B p q) : LeftMove A B q p := by
  obtain ⟨u,hu,he,hf,hh⟩ := h
  let t := A.mate (p.1.val.1,u)
  have ht : (q.1.val.1,t.2)=t := Prod.ext he rfl
  refine ⟨t.2,?_,?_,hf.symm,hh.symm⟩
  · rw [he]
    exact hh.trans (hu.trans (A.mate_height (p.1.val.1,u)).symm)
  · rw [ht,A.mate_involutive]

theorem RightMove.symm {p q : Port A B} (h : RightMove A B p q) : RightMove A B q p := by
  obtain ⟨u,hu,he,hf,hh⟩ := h
  let t := B.mate (p.1.val.2,u)
  have ht : (q.1.val.2,t.2)=t := Prod.ext hf rfl
  refine ⟨t.2,?_,he.symm,?_,hh.symm⟩
  · rw [hf]
    exact hh.trans (hu.trans (B.mate_height (p.1.val.2,u)).symm)
  · rw [ht,B.mate_involutive]

theorem LeftMove.unique {p q r : Port A B} (hq : LeftMove A B p q) (hr : LeftMove A B p r) : q=r := by
  obtain ⟨u,hu,he,hf,hh⟩ := hq
  obtain ⟨v,hv,ie,jf,jh⟩ := hr
  have huv : u=v := A.height_injective _ (hu.symm.trans hv)
  exact port_ext A B (he.trans (by simpa only [huv] using ie.symm)) (hf.trans jf.symm) (hh.trans jh.symm)

theorem RightMove.unique {p q r : Port A B} (hq : RightMove A B p q) (hr : RightMove A B p r) : q=r := by
  obtain ⟨u,hu,he,hf,hh⟩ := hq
  obtain ⟨v,hv,ie,jf,jh⟩ := hr
  have huv : u=v := B.height_injective _ (hu.symm.trans hv)
  exact port_ext A B (he.trans ie.symm) (hf.trans (by simpa only [huv] using jf.symm)) (hh.trans jh.symm)

theorem LeftMove.boundary {p q : Port A B} (h : LeftMove A B p q)
    (hb : portHeight A B p=0 ∨ portHeight A B p=H) : q=p := by
  obtain ⟨u,hu,he,hf,hh⟩ := h
  have hm : A.mate (p.1.val.1,u)=(p.1.val.1,u) := (A.mate_fixed _).mpr
    (hb.imp (fun h => hu.symm.trans h) (fun h => hu.symm.trans h))
  exact port_ext A B (by simpa only [hm] using he) hf hh

theorem RightMove.boundary {p q : Port A B} (h : RightMove A B p q)
    (hb : portHeight A B p=0 ∨ portHeight A B p=H) : q=p := by
  obtain ⟨u,hu,he,hf,hh⟩ := h
  have hm : B.mate (p.1.val.2,u)=(p.1.val.2,u) := (B.mate_fixed _).mpr
    (hb.imp (fun h => hu.symm.trans h) (fun h => hu.symm.trans h))
  exact port_ext A B he (by simpa only [hm] using hf) hh

theorem LeftMove.fixed {p : Port A B} (h : LeftMove A B p p) :
    portHeight A B p=0 ∨ portHeight A B p=H := by
  obtain ⟨u,hu,he,_,_⟩ := h
  have hm := (A.mate_edge_eq_iff _).mp he.symm
  exact ((A.mate_fixed _).mp hm).imp (fun h => hu.trans h) (fun h => hu.trans h)

theorem RightMove.fixed {p : Port A B} (h : RightMove A B p p) :
    portHeight A B p=0 ∨ portHeight A B p=H := by
  obtain ⟨u,hu,_,hf,_⟩ := h
  have hm := (B.mate_edge_eq_iff _).mp hf.symm
  exact ((B.mate_fixed _).mp hm).imp (fun h => hu.trans h) (fun h => hu.trans h)

theorem Incidence.unique (hsep : Separated A B) {p q r : Port A B}
    (hq : Incidence A B p q) (hr : Incidence A B p r) : q=r := by
  rcases hq with hq|hq <;> rcases hr with hr|hr
  · exact hq.unique A B hr
  · have hqfull := hq
    have hrfull := hr
    obtain ⟨u,hu,_⟩ := hq
    obtain ⟨v,hv,_⟩ := hr
    have hb := (hsep _ _ u v (hu.symm.trans hv)).imp (fun h => hu.trans h) (fun h => hu.trans h)
    exact (hqfull.boundary A B hb).trans (hrfull.boundary A B hb).symm
  · have hqfull := hq
    have hrfull := hr
    obtain ⟨u,hu,_⟩ := hr
    obtain ⟨v,hv,_⟩ := hq
    have hb := (hsep _ _ u v (hu.symm.trans hv)).imp (fun h => hu.trans h) (fun h => hu.trans h)
    exact (hqfull.boundary A B hb).trans (hrfull.boundary A B hb).symm
  · exact hq.unique A B hr

theorem exists_incidence (hsep : Separated A B) (p : Port A B) : ∃q,Incidence A B p q := by
  have hleft (u : Bool) (hu : portHeight A B p=A.height p.1.val.1 u) : ∃q,LeftMove A B p q := by
    by_cases hb : portHeight A B p=0 ∨ portHeight A B p=H
    · have hm := (A.mate_fixed (p.1.val.1,u)).mpr
        (hb.imp (fun h => hu.symm.trans h) (fun h => hu.symm.trans h))
      exact ⟨p,u,hu,by rw [hm],rfl,rfl⟩
    · have hh := not_or.mp hb
      obtain ⟨q,he,hf,hq⟩ := exists_left_replacement A B hsep p u hu hh.1 hh.2
      exact ⟨q,u,hu,he,hf,hq⟩
  have hright (u : Bool) (hu : portHeight A B p=B.height p.1.val.2 u) : ∃q,RightMove A B p q := by
    by_cases hb : portHeight A B p=0 ∨ portHeight A B p=H
    · have hm := (B.mate_fixed (p.1.val.2,u)).mpr
        (hb.imp (fun h => hu.symm.trans h) (fun h => hu.symm.trans h))
      exact ⟨p,u,hu,rfl,by rw [hm],rfl⟩
    · have hh := not_or.mp hb
      obtain ⟨q,he,hf,hq⟩ := exists_right_replacement A B hsep p u hu hh.1 hh.2
      exact ⟨q,u,hu,he,hf,hq⟩
  rcases portHeight_origin A B p with h|h|h|h
  · obtain ⟨q,hq⟩ := hleft false h; exact ⟨q,Or.inl hq⟩
  · obtain ⟨q,hq⟩ := hleft true h; exact ⟨q,Or.inl hq⟩
  · obtain ⟨q,hq⟩ := hright false h; exact ⟨q,Or.inr hq⟩
  · obtain ⟨q,hq⟩ := hright true h; exact ⟨q,Or.inr hq⟩

noncomputable def vertexMate (hsep : Separated A B) (p : Port A B) : Port A B :=
  (exists_incidence A B hsep p).choose

theorem vertexMate_incidence (hsep : Separated A B) (p : Port A B) :
    Incidence A B p (vertexMate A B hsep p) := (exists_incidence A B hsep p).choose_spec

theorem vertexMate_involutive (hsep : Separated A B) : Function.Involutive (vertexMate A B hsep) := by
  intro p
  apply Incidence.unique A B hsep (vertexMate_incidence A B hsep (vertexMate A B hsep p))
  rcases vertexMate_incidence A B hsep p with h|h
  · exact Or.inl (h.symm A B)
  · exact Or.inr (h.symm A B)

theorem vertexMate_fixed (hsep : Separated A B) (p : Port A B) :
    vertexMate A B hsep p=p ↔ portHeight A B p=0 ∨ portHeight A B p=H := by
  constructor
  · intro he
    have h := vertexMate_incidence A B hsep p
    rw [he] at h
    exact h.elim (LeftMove.fixed A B) (RightMove.fixed A B)
  · intro hb
    exact (vertexMate_incidence A B hsep p).elim (fun h => h.boundary A B hb) (fun h => h.boundary A B hb)

end HiddenCircuits.Approximation.CanonicalPaths.MountainSystem
