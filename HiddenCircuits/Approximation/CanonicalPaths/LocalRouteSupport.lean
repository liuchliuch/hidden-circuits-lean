import HiddenCircuits.Approximation.CanonicalPaths.LocalRoutes

/-! Proof of confined-route support and literal vertex traces. -/
namespace HiddenCircuits.Approximation.CanonicalPaths.LocalRoutes
variable {n : ℕ} {R : Fin n → Fin n → Prop}

theorem Move.eq_outside {S : Finset (Fin n)} {p q : State R} (h : Move S p q)
    (i : Fin n) (hi : i∉S) : q.val i=p.val i := by
  obtain ⟨a,ha,b,hb,h⟩ := h
  have hia : i≠a := fun he => hi (he.symm ▸ ha)
  have hib : i≠b := fun he => hi (he.symm ▸ hb)
  simp only [h,Equiv.trans_apply,Equiv.swap_apply_of_ne_of_ne hia hib]

theorem Route.eq_outside {S : Finset (Fin n)} {p q : State R} {k : ℕ} (h : Route S p q k)
    (i : Fin n) (hi : i∉S) : q.val i=p.val i := by
  induction h with
  | nil p => rfl
  | step hm hr ih => exact ih.trans (hm.eq_outside i hi)

theorem Route.enlarge {S T : Finset (Fin n)} (hst : S⊆T)
    {p q : State R} {k : ℕ} (h : Route S p q k) : Route T p q k := by
  induction h with
  | nil p => exact Route.nil p
  | step hm hr ih =>
    obtain ⟨a,ha,b,hb,he⟩ := hm
    exact Route.step ⟨a,hst ha,b,hst hb,he⟩ ih

theorem route_of_agree_outside (hR : Ordered R) (p q : State R) (S : Finset (Fin n))
    (hout : ∀i,i∉S → p.val i=q.val i) : ∃ k ≤ S.card,Route S p q k := by
  have hsub : disagreements p q⊆S := by
    intro i hi
    by_contra hn
    exact ((mem_disagreements p q i).mp hi) (hout i hn)
  obtain ⟨k,hk,hr⟩ := exists_confined_route hR p q
  exact ⟨k,hk.trans (Finset.card_le_card hsub),hr.enlarge hsub⟩

theorem Route.vertices {S : Finset (Fin n)} {p q : State R} {k : ℕ} (h : Route S p q k) :
    ∃ v : Fin (k+1) → State R,v 0=p ∧ v (Fin.last k)=q ∧
      (∀i : Fin k,Move S (v i.castSucc) (v i.succ)) ∧
      ∀i j,j∉S → (v i).val j=p.val j := by
  induction h with
  | nil p =>
    exact ⟨fun _ => p,rfl,rfl,fun i => Fin.elim0 i,fun _ _ _ => rfl⟩
  | @step p q r k hm hr ih =>
    obtain ⟨v,hv₀,hvlast,hvmove,hvoutside⟩ := ih
    refine ⟨Fin.cons p v,rfl,?_,?_,?_⟩
    · simpa using hvlast
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [hv₀] using hm
      · simpa using hvmove j
    · intro i j hj
      refine Fin.cases rfl (fun a => ?_) i
      exact (hvoutside a j hj).trans (hm.eq_outside j hj)

end HiddenCircuits.Approximation.CanonicalPaths.LocalRoutes
