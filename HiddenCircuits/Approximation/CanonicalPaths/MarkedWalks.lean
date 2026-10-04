import HiddenCircuits.Approximation.CanonicalPaths.CompanionRoutes
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
namespace HiddenCircuits.Approximation.CanonicalPaths.LocalRoutes
variable {n : ℕ} {R : Fin n → Fin n → Prop}
theorem Move.mono {S T : Finset (Fin n)} (hst : S⊆T) {p q : State R} (h : Move S p q) : Move T p q := by
  rcases h with ⟨i,hi,j,hj,he⟩
  exact ⟨i,hst hi,j,hst hj,he⟩
theorem Route.mono {S T : Finset (Fin n)} (hst : S⊆T) {p q : State R} {k : ℕ} (h : Route S p q k) :
    Route T p q k := by
  induction h with
  | nil p => exact Route.nil p
  | step hm hr ih => exact Route.step (hm.mono hst) ih
theorem MarkedRoute.mono {S T : Finset (Fin n)} {Good Good' : State R → Prop}
    (hst : S⊆T) (hg : ∀ p, Good p → Good' p) {p q : State R} {k : ℕ}
    (h : MarkedRoute S Good p q k) : MarkedRoute T Good' p q k := by
  induction h with
  | nil p hp => exact MarkedRoute.nil p (hg p hp)
  | step hp hm hr ih => exact MarkedRoute.step (hg _ hp) (hm.mono hst) ih
theorem marked_route_of_walk {V : Type*} {G : SimpleGraph V} (state : V → State R)
    (Good : State R → Prop) (C : ℕ) (good : ∀ v, Good (state v))
    (step : ∀ u v, G.Adj u v → ∃ k ≤ C, MarkedRoute Finset.univ Good (state u) (state v) k)
    {u v : V} (walk : G.Walk u v) :
    ∃ k ≤ C*walk.length, MarkedRoute Finset.univ Good (state u) (state v) k := by
  induction walk with
  | nil => exact ⟨0,by simp,MarkedRoute.nil _ (good _)⟩
  | @cons u v w huv tail ih =>
    obtain ⟨a,ha,hr⟩ := step u v huv
    obtain ⟨b,hb,ht⟩ := ih
    refine ⟨a+b,?_,hr.append ht⟩
    simp only [SimpleGraph.Walk.length_cons]
    nlinarith
theorem MarkedRoute.vertices {S : Finset (Fin n)} {Good : State R → Prop}
    {p q : State R} {k : ℕ} (h : MarkedRoute S Good p q k) :
    ∃ v : Fin (k+1) → State R, v 0=p ∧ v (Fin.last k)=q ∧
      (∀ i : Fin k, Move S (v i.castSucc) (v i.succ)) ∧ ∀ i, Good (v i) := by
  induction h with
  | nil p hp =>
    refine ⟨fun _ => p,rfl,rfl,?_,?_⟩
    · exact fun i => Fin.elim0 i
    · exact fun _ => hp
  | @step p q r k hp hm hr ih =>
    obtain ⟨v,hv₀,hvlast,hvmove,hvGood⟩ := ih
    refine ⟨Fin.cons p v,rfl,?_,?_,?_⟩
    · simpa using hvlast
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [hv₀] using hm
      · simpa using hvmove j
    · exact Fin.cases hp (fun i => by simpa using hvGood i)
end HiddenCircuits.Approximation.CanonicalPaths.LocalRoutes
