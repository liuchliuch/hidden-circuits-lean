import HiddenCircuits.Approximation.CanonicalPaths.LocalRouteSupport
namespace HiddenCircuits.Approximation.CanonicalPaths.LocalRoutes
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {R : Fin n → Fin n → Prop}
def HasCompanion (p q z : State R) (d : ℕ) : Prop :=
  ∃ w : State R, ∃ S : Finset (Fin n), S.card ≤ d ∧
    ∀ i, i∉S → ({z.val i,w.val i} : Finset (Fin n))={p.val i,q.val i}
theorem HasCompanion.initial (p q : State R) (d : ℕ) : HasCompanion p q p d := by
  exact ⟨q,∅,by simp,fun i _ => rfl⟩
theorem HasCompanion.final (p q : State R) (d : ℕ) : HasCompanion p q q d := by
  exact ⟨p,∅,by simp,fun i _ => Finset.pair_comm _ _⟩
theorem HasCompanion.mono {p q z : State R} {d e : ℕ} (h : HasCompanion p q z d)
    (hde : d ≤ e) : HasCompanion p q z e := by
  obtain ⟨w,S,hS,h⟩ := h
  exact ⟨w,S,hS.trans hde,h⟩
theorem HasCompanion.of_eq_outside {p q z z' : State R} {d e : ℕ} (h : HasCompanion p q z d)
    (T : Finset (Fin n)) (hT : T.card ≤ e) (hz : ∀ i, i∉T → z'.val i=z.val i) :
    HasCompanion p q z' (d+e) := by
  obtain ⟨w,S,hS,h⟩ := h
  refine ⟨w,S∪T,(Finset.card_union_le S T).trans (Nat.add_le_add hS hT),?_⟩
  intro i hi
  have hh : i∉S ∧ i∉T := by simpa using hi
  rw [hz i hh.2]
  exact h i hh.1
inductive MarkedRoute (S : Finset (Fin n)) (Good : State R → Prop) :
    State R → State R → ℕ → Prop
  | nil (p) : Good p → MarkedRoute S Good p p 0
  | step {p q r k} : Good p → Move S p q → MarkedRoute S Good q r k → MarkedRoute S Good p r (k+1)
theorem MarkedRoute.toRoute {S : Finset (Fin n)} {Good : State R → Prop}
    {p q : State R} {k : ℕ} (h : MarkedRoute S Good p q k) : Route S p q k := by
  induction h with
  | nil p hp => exact Route.nil p
  | step hp hm hr ih => exact Route.step hm ih
theorem MarkedRoute.append {S : Finset (Fin n)} {Good : State R → Prop}
    {p q r : State R} {k l : ℕ} (h : MarkedRoute S Good p q k) (h' : MarkedRoute S Good q r l) :
    MarkedRoute S Good p r (k+l) := by
  induction h with
  | nil p hp => simpa using h'
  | step hp hm hr ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using MarkedRoute.step hp hm (ih h')
theorem Route.mark {S : Finset (Fin n)} {p q : State R} {k : ℕ} (h : Route S p q k)
    (Good : State R → Prop) (hg : ∀ z, (∀ i, i∉S → z.val i=p.val i) → Good z) :
    MarkedRoute S Good p q k := by
  induction h with
  | nil p => exact MarkedRoute.nil p (hg p (fun _ _ => rfl))
  | @step p q r k hm hr ih =>
    refine MarkedRoute.step (hg p (fun _ _ => rfl)) hm (ih ?_)
    intro z hz
    exact hg z (fun i hi => (hz i hi).trans (hm.eq_outside i hi))
theorem Route.mark_companion {S : Finset (Fin n)} {p q z z' : State R} {k d e : ℕ}
    (h : Route S z z' k) (hc : HasCompanion p q z d) (hS : S.card ≤ e) :
    MarkedRoute S (fun w => HasCompanion p q w (d+e)) z z' k := by
  apply h.mark
  intro w hw
  exact hc.of_eq_outside S hS hw
end HiddenCircuits.Approximation.CanonicalPaths.LocalRoutes
