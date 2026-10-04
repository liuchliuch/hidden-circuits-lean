import HiddenCircuits.Approximation.CanonicalPaths.GlobalRoutes
import HiddenCircuits.Approximation.CanonicalPaths.TrafficEncoding
import HiddenCircuits.Approximation.FiniteChains.Sampling
namespace HiddenCircuits.Approximation.CanonicalPaths
open LocalRoutes FiniteChains
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {n : ℕ} (E : MonotoneEndpoints n)
abbrev MatchingState := FiniteChains.MonotoneSwitch.ColumnState E
def routeLength (n : ℕ) : ℕ := n*(8*n*n+4)
def routeTrafficFactor (n : ℕ) : ℕ := routeLength n*((n+1)^6*n^6*n^6*n*n)
/-- Every recorded edge comes from a genuine admissible switch. -/
theorem constructed_path (P Q : MatchingState E) :
    ∃ path : FiniteChains.Path P Q, path.length ≤ routeLength n ∧
      (∀ i : Fin path.length, Move (R := fun col row => Allowed E row col) Finset.univ (path.vertex i.castSucc) (path.vertex i.succ)) ∧
      ∀ i : Fin path.length, TrafficGood E P Q (path.vertex i.castSucc) := by
  by_cases hn : 0<n
  · obtain ⟨l,hl,hr⟩ := all_pairs_marked_route E P Q hn
    obtain ⟨v,hv₀,hvlast,hvmove,hvGood⟩ := hr.vertices
    exact ⟨⟨l,v,hv₀,hvlast⟩,hl,hvmove,fun i => hvGood i.castSucc⟩
  · have hz : n=0 := by omega
    have he : P=Q := by
      apply Subtype.ext
      apply Equiv.ext
      intro i
      have hi := i.isLt
      omega
    refine ⟨⟨0,fun _ => P,rfl,he⟩,by simp [routeLength],?_,?_⟩
    · exact fun i => Fin.elim0 i
    · exact fun i => Fin.elim0 i
noncomputable def flowPath (P Q : MatchingState E) : FiniteChains.Path P Q :=
  (constructed_path E P Q).choose
theorem flowPath_length (P Q : MatchingState E) : (flowPath E P Q).length ≤ routeLength n :=
  (constructed_path E P Q).choose_spec.1
theorem flowPath_move (P Q : MatchingState E) (i : Fin (flowPath E P Q).length) :
    Move (R := fun col row => Allowed E row col) Finset.univ ((flowPath E P Q).vertex i.castSucc) ((flowPath E P Q).vertex i.succ) :=
  (constructed_path E P Q).choose_spec.2.1 i
theorem flowPath_good (P Q : MatchingState E) (i : Fin (flowPath E P Q).length) :
    TrafficGood E P Q ((flowPath E P Q).vertex i.castSucc) :=
  (constructed_path E P Q).choose_spec.2.2 i
theorem flowPath_edgeCount_le (P Q a b : MatchingState E) :
    (flowPath E P Q).edgeCount a b ≤ routeLength n := by
  classical
  have h := Finset.card_filter_le (Finset.univ : Finset (Fin (flowPath E P Q).length))
    (fun i => (flowPath E P Q).vertex i.castSucc=a ∧ (flowPath E P Q).vertex i.succ=b)
  simp only [Finset.card_univ,Fintype.card_fin] at h
  unfold FiniteChains.Path.edgeCount
  convert h.trans (flowPath_length E P Q) using 1
  congr 1
  ext i
  simp
theorem flowPath_edgeCount_zero (P Q a b : MatchingState E) (hgood : ¬TrafficGood E P Q a) :
    (flowPath E P Q).edgeCount a b=0 := by
  classical
  unfold FiniteChains.Path.edgeCount
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have hp : (flowPath E P Q).vertex i.castSucc=a ∧ (flowPath E P Q).vertex i.succ=b := by
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hi
  have hg := flowPath_good E P Q i
  rw [hp.1] at hg
  exact hgood hg
theorem traffic_pairs_card (a : MatchingState E) :
    Fintype.card (TrafficEncoding.Pairs (R := fun col row => Allowed E row col) a 6)=
      ∑ P : MatchingState E, ∑ Q : MatchingState E, if TrafficGood E P Q a then 1 else 0 := by
  classical
  rw [← Fintype.sum_prod_type (fun t : MatchingState E × MatchingState E =>
    if TrafficGood E t.1 t.2 a then 1 else 0)]
  rw [Fintype.card_eq_nat_card]
  change Nat.card {t : MatchingState E × MatchingState E // TrafficGood E t.1 t.2 a} = _
  rw [Nat.card_eq_fintype_card]
  simp only [Fintype.card_subtype,Finset.card_filter]
theorem flowPath_traffic (a b : MatchingState E) :
    FiniteChains.traffic (flowPath E) a b ≤ routeTrafficFactor n*Fintype.card (MatchingState E) := by
  have hc := TrafficEncoding.pairs_card_bound (R := fun col row => Allowed E row col) a 6
  calc
    FiniteChains.traffic (flowPath E) a b ≤
        ∑ P : MatchingState E, ∑ Q : MatchingState E,
          if TrafficGood E P Q a then routeLength n else 0 := by
      apply Finset.sum_le_sum
      intro P _
      apply Finset.sum_le_sum
      intro Q _
      by_cases h : TrafficGood E P Q a
      · simpa only [if_pos h] using flowPath_edgeCount_le E P Q a b
      · simp only [if_neg h,flowPath_edgeCount_zero E P Q a b h,le_refl]
    _ = routeLength n*Fintype.card (TrafficEncoding.Pairs (R := fun col row => Allowed E row col) a 6) := by
      rw [traffic_pairs_card]
      simp_rw [Finset.mul_sum,mul_ite,mul_one,mul_zero]
    _ ≤ routeLength n*(Fintype.card (MatchingState E)*((n+1)^6*n^6*n^6)*n*n) :=
      Nat.mul_le_mul_left _ hc
    _ = routeTrafficFactor n*Fintype.card (MatchingState E) := by unfold routeTrafficFactor; ring
/-- The complete concrete family accepted by the proved finite-chain analysis. -/
noncomputable def monotoneCanonicalPaths :
    FiniteChains.CanonicalPaths (FiniteChains.MonotoneSwitch.columnChain E (Nat.size n))
      (routeTrafficFactor n) (routeLength n) (8*(n+1)^2) where
  path := flowPath E
  length_le := flowPath_length E
  traffic_le := flowPath_traffic E
  Q_pos := by positivity
  transition_lower P Q i := FiniteChains.MonotoneSwitch.move_chain_lower E (flowPath_move E P Q i)
end HiddenCircuits.Approximation.CanonicalPaths
