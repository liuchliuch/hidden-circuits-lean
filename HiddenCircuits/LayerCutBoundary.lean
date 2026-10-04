import HiddenCircuits.LayerCutDecomposition

namespace HiddenCircuits.Layered
open HiddenCircuits.DH

 theorem pair_mem_leftDomain_ne {p : ℕ} (e : PartialPairs (Fin (2*p)) (Fin (2*p))) (x : Fin (2*p)) :
    x ∈ e.leftDomain ↔ e.left x ≠ none := by
  rw [PartialPairs.mem_leftDomain]
  exact Option.ne_none_iff_exists'.symm
 theorem pair_mem_rightDomain_ne {p : ℕ} (e : PartialPairs (Fin (2*p)) (Fin (2*p))) (x : Fin (2*p)) :
    x ∈ e.rightDomain ↔ e.right x ≠ none := by
  rw [PartialPairs.mem_rightDomain]
  exact Option.ne_none_iff_exists'.symm

/-- The actual crossing pairs in a transfer step, with precisely the two selected domains. -/
def CutStep {p : ℕ} (R : UnweightedCut p) (S U : State (2*p) p) :=
  {e : PartialPairs (Fin (2*p)) (Fin (2*p)) //
    e.leftDomain = S.val ∧ e.rightDomain = U.halfComplement.val ∧
      ∀ x y, e.left x = some y → R x y = true}

noncomputable instance {p : ℕ} (R : UnweightedCut p) (S U : State (2*p) p) : Fintype (CutStep R S U) := by
  classical
  unfold CutStep
  infer_instance

namespace CutData
variable {p : ℕ} {R : UnweightedCut p} {w : List (UnweightedCut p)}

def Incoming (d : CutData R w) (v : Vertices p w.length) : Prop :=
  ∃ y, first p w.length y=v ∧ d.pairs.right y ≠ none

 theorem incoming_tail_none (d : CutData R w) (v : Vertices p w.length) (h : d.Incoming v) :
    d.tail.val v = none := by
  obtain ⟨y,rfl,hy⟩ := h
  obtain ⟨x,hx⟩ := Option.ne_none_iff_exists'.mp hy
  exact (d.valid x y ((d.pairs.symm x y).mpr hx)).1

 theorem incoming_iff_bind_ne (d : CutData R w) (v : Vertices p w.length) :
    d.Incoming v ↔ (firstDecode p w.length v).bind d.pairs.right ≠ none := by
  constructor
  · rintro ⟨y,hy,hn⟩
    rw [(firstDecode_some p w.length v y).mpr hy.symm,Option.bind_some]
    exact hn
  · intro hn
    cases hd : firstDecode p w.length v with
    | none => simp [hd] at hn
    | some y =>
      refine ⟨y,((firstDecode_some p w.length v y).mp hd).symm,?_⟩
      simpa only [hd,Option.bind_some] using hn

 theorem matching_left_none (d : CutData R w) (x : Fin (2*p)) :
    d.matching.val (.inl x)=none ↔ d.pairs.left x=none := by
  change d.toJoinData.partner (.inl x) = none ↔ _
  simp only [JoinData.partner,CutData.toJoinData,emptyMatching]
  simp

 theorem matching_right_none (d : CutData R w) (v : Vertices p w.length) :
    d.matching.val (.inr v)=none ↔ d.tail.val v=none ∧ ¬d.Incoming v := by
  rw [d.incoming_iff_bind_ne]
  simp only [not_not]
  change d.toJoinData.partner (.inr v) = none ↔ _
  simp only [JoinData.partner,CutData.toJoinData]
  cases d.tail.val v <;> simp

 theorem boundary_iff (d : CutData R w) (S T : State (2*p) p) :
    BoundaryCondition (R::w) S T d.matching ↔
      (∀ x, d.pairs.left x=none ↔ x ∉ S.val) ∧
      (∀ v, d.tail.val v=none ∧ ¬d.Incoming v ↔
        ∃ y, last p w.length y=v ∧ y ∈ T.val) := by
  constructor
  · intro h
    exact ⟨fun x => (d.matching_left_none x).symm.trans ((h (.inl x)).trans (ghost_cons_left R w S T x)),
      fun v => (d.matching_right_none v).symm.trans ((h (.inr v)).trans (ghost_cons_right R w S T v))⟩
  · rintro ⟨hl,hr⟩ v
    cases v with
    | inl x => exact (d.matching_left_none x).trans ((hl x).trans (ghost_cons_left R w S T x).symm)
    | inr v => exact (d.matching_right_none v).trans ((hr v).trans (ghost_cons_right R w S T v).symm)

 theorem leftDomain_eq (d : CutData R w) (S T : State (2*p) p)
    (h : BoundaryCondition (R::w) S T d.matching) : d.pairs.leftDomain=S.val := by
  ext x
  rw [pair_mem_leftDomain_ne]
  have hh := (d.boundary_iff S T).mp h |>.1 x
  exact not_congr hh |>.trans not_not

/-- Half filling at the first boundary forces exactly p crossing edges and hence a
half-filled outgoing state at the next layer. -/
def nextState (d : CutData R w) (S T : State (2*p) p)
    (h : BoundaryCondition (R::w) S T d.matching) : State (2*p) p :=
  ⟨d.pairs.rightDomainᶜ,by
    have hc := d.pairs.domain_card_eq
    rw [d.leftDomain_eq S T h,S.property] at hc
    rw [Finset.card_compl,Fintype.card_fin]
    omega⟩

 theorem rightDomain_nextState (d : CutData R w) (S T : State (2*p) p)
    (h : BoundaryCondition (R::w) S T d.matching) :
    d.pairs.rightDomain = (d.nextState S T h).halfComplement.val := by
  simp only [nextState,State.halfComplement_val,compl_compl]

 theorem ghost_of_rightDomain (d : CutData R w) (U T : State (2*p) p)
    (hd : d.pairs.rightDomain=U.halfComplement.val) (v : Vertices p w.length) :
    Ghost w U T v ↔ d.Incoming v ∨ (∃ y, last p w.length y=v ∧ y ∈ T.val) := by
  have hx (x : Fin (2*p)) : x ∉ U.val ↔ d.pairs.right x ≠ none := by
    rw [← pair_mem_rightDomain_ne,hd,State.halfComplement_val,Finset.mem_compl]
  simp only [Ghost,hx,Incoming]

 theorem tail_boundary (d : CutData R w) (S T : State (2*p) p)
    (h : BoundaryCondition (R::w) S T d.matching) :
    BoundaryCondition w (d.nextState S T h) T d.tail := by
  intro v
  rw [d.ghost_of_rightDomain _ T (d.rightDomain_nextState S T h) v]
  have hr := (d.boundary_iff S T).mp h |>.2 v
  constructor
  · intro ht
    by_cases hi : d.Incoming v
    · exact Or.inl hi
    · exact Or.inr (hr.mp ⟨ht,hi⟩)
  · rintro (hi | hl)
    · exact d.incoming_tail_none v hi
    · exact (hr.mpr hl).1

end CutData

/-- The first-layer deletion set and final-layer deletion set cannot overlap in a
boundary matching, including the zero-cut base case where endpoint states coincide. -/
theorem boundary_ghosts_disjoint {p : ℕ} {w : List (UnweightedCut p)}
    {U T : State (2*p) p} (m : BoundaryMatching w U T) (v : Vertices p w.length) :
    ¬ ((∃ y, first p w.length y=v ∧ y ∉ U.val) ∧
      (∃ z, last p w.length z=v ∧ z ∈ T.val)) := by
  rintro ⟨⟨y,hy,hyU⟩,⟨z,hz,hzT⟩⟩
  have hh := first_eq_last y z (hy.trans hz.symm)
  have hw : w=[] := by simpa using hh.1
  subst w
  have he := boundary_nil_states U T m
  exact hyU (he ▸ (hh.2.symm ▸ hzT))

namespace CutStep
variable {p : ℕ} {R : UnweightedCut p} {w : List (UnweightedCut p)}
    {S U T : State (2*p) p}

/-- A chosen cut bijection and tail matching determine actual valid first-cut data. -/
def toCutData (e : CutStep R S U) (m : BoundaryMatching w U T) : CutData R w where
  tail := m.val
  pairs := e.val
  valid x y h := by
    have hr : y ∈ e.val.rightDomain :=
      (PartialPairs.mem_rightDomain _ _).mpr ⟨x,(e.val.symm x y).mp h⟩
    rw [e.property.2.1,State.halfComplement_val,Finset.mem_compl] at hr
    exact ⟨(m.property (first p w.length y)).mpr (Or.inl ⟨y,rfl,hr⟩),e.property.2.2 x y h⟩

 theorem toCutData_boundary (e : CutStep R S U) (m : BoundaryMatching w U T) :
    BoundaryCondition (R::w) S T (e.toCutData m).matching := by
  let d := e.toCutData m
  apply (d.boundary_iff S T).mpr
  constructor
  · intro x
    have hmem : x ∈ d.pairs.leftDomain ↔ x ∈ S.val := by rw [show d.pairs=e.val from rfl,e.property.1]
    have hne := (pair_mem_leftDomain_ne d.pairs x).symm.trans hmem
    simpa only [not_not] using hne.not
  · intro v
    have hd : d.pairs.rightDomain = U.halfComplement.val := e.property.2.1
    have hg := d.ghost_of_rightDomain U T hd v
    constructor
    · rintro ⟨ht,hn⟩
      have hghost := (m.property v).mp ht
      exact (hg.mp hghost).resolve_left hn
    · intro hl
      refine ⟨(m.property v).mpr (hg.mpr (Or.inr hl)),?_⟩
      rintro ⟨y,hy,hyn⟩
      have hym : y ∈ d.pairs.rightDomain := (pair_mem_rightDomain_ne _ _).mpr hyn
      rw [hd,State.halfComplement_val,Finset.mem_compl] at hym
      exact boundary_ghosts_disjoint m v ⟨⟨y,hy,hym⟩,hl⟩

end CutStep
end HiddenCircuits.Layered
