import HiddenCircuits.Approximation.CanonicalPaths.ComponentLifting

/-! Exact route functoriality and actual embedded-switch identities. -/
namespace HiddenCircuits.Approximation.CanonicalPaths.LocalRoutes
variable {m n : ℕ} {r : Fin m → Fin m → Prop} {R : Fin n → Fin n → Prop}

theorem Route.map (f : State r → State R) {S : Finset (Fin m)} {T : Finset (Fin n)}
    (hm : ∀p q,Move S p q → Move T (f p) (f q))
    {p q : State r} {k : ℕ} (h : Route S p q k) : Route T (f p) (f q) k := by
  induction h with
  | nil p => exact Route.nil _
  | step hmove htail ih => exact Route.step (hm _ _ hmove) ih

theorem MarkedRoute.map (f : State r → State R) {S : Finset (Fin m)} {T : Finset (Fin n)}
    {Good : State r → Prop} {Good' : State R → Prop}
    (hm : ∀p q,Move S p q → Move T (f p) (f q))
    (hg : ∀p,Good p → Good' (f p))
    {p q : State r} {k : ℕ} (h : MarkedRoute S Good p q k) :
    MarkedRoute T Good' (f p) (f q) k := by
  induction h with
  | nil p hp => exact MarkedRoute.nil _ (hg _ hp)
  | step hp hmove htail ih => exact MarkedRoute.step (hg _ hp) (hm _ _ hmove) ih

theorem MarkedRoute.last_good {S : Finset (Fin m)} {Good : State r → Prop}
    {p q : State r} {k : ℕ} (h : MarkedRoute S Good p q k) : Good q := by
  induction h with
  | nil p hp => exact hp
  | step hp hmove htail ih => exact ih

theorem MarkedRoute.reverse {S : Finset (Fin m)} {Good : State r → Prop}
    {p q : State r} {k : ℕ} (h : MarkedRoute S Good p q k) : MarkedRoute S Good q p k := by
  induction h with
  | nil p hp => exact MarkedRoute.nil _ hp
  | step hp hmove htail ih =>
    simpa using ih.append (MarkedRoute.step ih.last_good hmove.symm (MarkedRoute.nil _ hp))

theorem liftState_move (columns : Fin m ↪ Fin n) (rows : Fin m → Fin n)
    (baseline : State R) (source : Equiv.Perm (Fin m))
    (hbase : ∀i,baseline.val (columns i)=rows (source i))
    (hvalid : ∀i j,r i j → R (columns i) (rows j))
    {p q : State r} (h : Move Finset.univ p q) :
    Move Finset.univ (liftState columns rows baseline source hbase hvalid p)
      (liftState columns rows baseline source hbase hvalid q) := by
  obtain ⟨a,ha,b,hb,he⟩ := h
  refine ⟨columns a,Finset.mem_univ _,columns b,Finset.mem_univ _,?_⟩
  change liftPermutation columns baseline.val source q.val=_
  rw [he]
  exact liftPermutation_swap columns baseline.val source p.val a b

end HiddenCircuits.Approximation.CanonicalPaths.LocalRoutes
