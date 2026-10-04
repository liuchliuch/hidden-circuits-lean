import HiddenCircuits.CutStepCount

/-! The actual layered-graph perfect-matching/state-path bijection and transfer identity. -/
namespace HiddenCircuits.Layered

/-- Equality of dependent state packages follows from equality of the state and
of the two underlying data objects; proof fields carry no additional choices. -/
theorem sigma_pair_subtype_ext {ι α β : Type*} {P : ι → α → Prop} {Q : ι → β → Prop}
    (x y : Σ i : ι, {a // P i a} × {b // Q i b})
    (hi : x.1=y.1) (ha : x.2.1.val=y.2.1.val) (hb : x.2.2.val=y.2.2.val) : x=y := by
  rcases x with ⟨i,⟨a,ha'⟩,⟨b,hb'⟩⟩
  rcases y with ⟨j,⟨c,hc'⟩,⟨d,hd'⟩⟩
  dsimp only at hi ha hb
  subst j
  subst c
  subst d
  rfl

abbrev ConsBoundaryData {p : ℕ} (R : UnweightedCut p) (w : List (UnweightedCut p))
    (S T : State (2*p) p) :=
  {d : CutData R w // BoundaryCondition (R::w) S T d.matching}

/-- Restrict the genuine first-cut graph matching bijection to the exact boundary condition. -/
def boundaryCutEquiv {p : ℕ} (R : UnweightedCut p) (w : List (UnweightedCut p))
    (S T : State (2*p) p) : BoundaryMatching (R::w) S T ≃ ConsBoundaryData R w S T :=
  (cutMatchingEquiv R w).subtypeEquiv (by
    intro m
    have he : ((cutMatchingEquiv R w) m).matching = m := (cutMatchingEquiv R w).left_inv m
    change BoundaryCondition (R::w) S T m ↔
      BoundaryCondition (R::w) S T (((cutMatchingEquiv R w) m).matching)
    rw [he])

/-- Extract the next half-filled state, its literal crossing edges, and the remaining matching. -/
def boundaryDataNext {p : ℕ} (R : UnweightedCut p) (w : List (UnweightedCut p))
    (S T : State (2*p) p) (d : ConsBoundaryData R w S T) :
    Σ U : State (2*p) p, CutStep R S U × BoundaryMatching w U T :=
  ⟨d.val.nextState S T d.property,
    ⟨d.val.pairs,d.val.leftDomain_eq S T d.property,d.val.rightDomain_nextState S T d.property,
      fun x y h => (d.val.valid x y h).2⟩,
    ⟨d.val.tail,d.val.tail_boundary S T d.property⟩⟩

def boundaryDataPrevious {p : ℕ} (R : UnweightedCut p) (w : List (UnweightedCut p))
    (S T : State (2*p) p)
    (d : Σ U : State (2*p) p, CutStep R S U × BoundaryMatching w U T) :
    ConsBoundaryData R w S T :=
  ⟨d.2.1.toCutData d.2.2,d.2.1.toCutData_boundary d.2.2⟩

 theorem boundaryData_previous_next {p : ℕ} (R : UnweightedCut p) (w : List (UnweightedCut p))
    (S T : State (2*p) p) (d : ConsBoundaryData R w S T) :
    boundaryDataPrevious R w S T (boundaryDataNext R w S T d) = d := by
  apply Subtype.ext
  apply CutData.ext <;> rfl

 theorem boundaryData_next_previous {p : ℕ} (R : UnweightedCut p) (w : List (UnweightedCut p))
    (S T : State (2*p) p)
    (d : Σ U : State (2*p) p, CutStep R S U × BoundaryMatching w U T) :
    boundaryDataNext R w S T (boundaryDataPrevious R w S T d) = d := by
  rcases d with ⟨U,e,m⟩
  have hU : (e.toCutData m).nextState S T (e.toCutData_boundary m) = U := by
    apply Subtype.ext
    change e.val.rightDomainᶜ=U.val
    rw [e.property.2.1,State.halfComplement_val,compl_compl]
  exact sigma_pair_subtype_ext _ _ hU rfl rfl

/-- Exact recursive decomposition into the next state and independent permitted cut
bijection. This is proved from actual graph matchings, with the p-edge invariant derived. -/
def boundaryConsEquiv {p : ℕ} (R : UnweightedCut p) (w : List (UnweightedCut p))
    (S T : State (2*p) p) :
    BoundaryMatching (R::w) S T ≃
      Σ U : State (2*p) p, CutStep R S U × BoundaryMatching w U T :=
  (boundaryCutEquiv R w S T).trans {
    toFun := boundaryDataNext R w S T
    invFun := boundaryDataPrevious R w S T
    left_inv := boundaryData_previous_next R w S T
    right_inv := boundaryData_next_previous R w S T }

/-- Every full-layer boundary matching has a unique sequence of states and cut bijections. -/
noncomputable def boundaryPathEquiv {p : ℕ} :
    (w : List (UnweightedCut p)) → (S T : State (2*p) p) →
      BoundaryMatching w S T ≃ TransferPath w S T
  | [], S,T => boundaryNilEquiv S T
  | R::w, S,T => (boundaryConsEquiv R w S T).trans
      (Equiv.sigmaCongrRight (fun U =>
        (CutStep.permutationEquiv R S U).prodCongr (boundaryPathEquiv w U T)))

/-- Section 3.2's claimed correspondence, now an actual equivalence with mathlib
perfect matching subgraphs of the retained simple-unweighted layered graph. -/
noncomputable def perfectMatchingPathEquiv {p : ℕ} (w : List (UnweightedCut p))
    (S T : State (2*p) p) :
    PerfectMatching (retainedGraph w S T) ≃ TransferPath w S T :=
  (boundaryPerfectEquiv w S T).symm.trans (boundaryPathEquiv w S T)

/-- The actual layered graph's perfect-matching count is precisely the product of
its consecutive permanental-complement transfers. -/
theorem matchingCount_eq_transferProduct {p : ℕ} (w : List (UnweightedCut p))
    (S T : State (2*p) p) :
    (matchingCount w S T : ℚ) = transferProduct w S T := by
  unfold matchingCount perfectMatchingCount
  rw [Fintype.card_congr (perfectMatchingPathEquiv w S T)]
  exact transferPath_card w S T

end HiddenCircuits.Layered
