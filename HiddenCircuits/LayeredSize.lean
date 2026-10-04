import HiddenCircuits.LayeredMatching

namespace HiddenCircuits.Layered

/-- The last-layer deletion set is literally a copy of the endpoint state T. -/
noncomputable def lastGhostEquiv {p : ℕ} (w : List (UnweightedCut p)) (T : State (2*p) p) :
    T.val ≃ {v : Vertices p w.length // ∃ x, last p w.length x=v ∧ x ∈ T.val} where
  toFun x := ⟨last p w.length x.val,x.val,rfl,x.property⟩
  invFun v := ⟨v.property.choose,v.property.choose_spec.2⟩
  left_inv x := by
    apply Subtype.ext
    exact last_injective p w.length ((show ∃ y, last p w.length y=last p w.length x.val ∧ y ∈ T.val
      from ⟨x.val,rfl,x.property⟩).choose_spec.1)
  right_inv v := Subtype.ext v.property.choose_spec.1

/-- Separate the retained first layer from all later retained vertices. -/
noncomputable def retainedConsEquiv {p : ℕ} (R : UnweightedCut p) (w : List (UnweightedCut p))
    (S T : State (2*p) p) :
    Retained (R::w) S T ≃ S.val ⊕
      {v : Vertices p w.length // ¬ ∃ x, last p w.length x=v ∧ x ∈ T.val} :=
  Equiv.subtypeSum.trans ((Equiv.subtypeEquivRight (fun x => by
    simpa only [not_not] using (ghost_cons_left R w S T x).not)).sumCongr
      (Equiv.subtypeEquivRight (fun v => (ghost_cons_right R w S T v).not)))

/-- With at least one cut, exactly p boundary vertices are retained at each end. -/
theorem retained_card_cons {p : ℕ} (R : UnweightedCut p) (w : List (UnweightedCut p))
    (S T : State (2*p) p) :
    Fintype.card (Retained (R::w) S T) = 2*p*(R::w).length := by
  classical
  have hlast : Fintype.card {v : Vertices p w.length // ∃ x, last p w.length x=v ∧ x ∈ T.val} = p := by
    rw [← Fintype.card_congr (lastGhostEquiv w T),Fintype.card_coe,T.property]
  rw [Fintype.card_congr (retainedConsEquiv R w S T),Fintype.card_sum,
    Fintype.card_coe,S.property,Fintype.card_subtype_compl,hlast,vertices_card]
  have hp : p ≤ (w.length+1)*(2*p) := by nlinarith
  have he : p+((w.length+1)*(2*p)-p) = (w.length+1)*(2*p) := by omega
  rw [he]
  simp only [List.length_cons]
  ring

 theorem retained_card {p : ℕ} (w : List (UnweightedCut p)) (hw : w≠[])
    (S T : State (2*p) p) : Fintype.card (Retained w S T) = 2*p*w.length := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons R w => exact retained_card_cons R w S T

end HiddenCircuits.Layered
