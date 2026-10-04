import HiddenCircuits.Approximation.SelfReduction.MatchingStates

/-! Computable deterministic residual-instance selection for actual matchings. -/
namespace HiddenCircuits.Approximation.SelfReduction
open scoped BigOperators

/-- The least retained vertex is a computable pivot. -/
def matchingPivot {b d : ℕ} (U : {U : Finset (Fin (b+1)) // U.card=2*(d+1)}) : U.val :=
  ⟨U.val.min' (Finset.card_pos.mp (by rw [U.property]; positivity)), Finset.min'_mem _ _⟩

theorem erased_card {b d : ℕ} (U : {U : Finset (Fin (b+1)) // U.card=2*(d+1)})
    (v : Fin (b+1)) (hv : v ∈ U.val) (hne : v ≠ (matchingPivot U).val) :
    ((U.val.erase (matchingPivot U).val).erase v).card=2*d := by
  have hu := (matchingPivot U).property
  have hv' : v ∈ U.val.erase (matchingPivot U).val := Finset.mem_erase.mpr ⟨hne,hv⟩
  rw [Finset.card_erase_of_mem hv', Finset.card_erase_of_mem hu, U.property]
  omega

/-- A branch is either the literal induced vertex-pair deletion or an explicit
rejected state. No test of the exact number of completions occurs here. -/
def matchingChild {b : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj] :
    MatchingState b → Fin (b+1) → MatchingState b
  | ⟨0,_⟩, _ => ⟨0,none⟩
  | ⟨d+1,none⟩, _ => ⟨d,none⟩
  | ⟨d+1,some U⟩, v =>
      if h : v ∈ U.val ∧ G.Adj (matchingPivot U).val v then
        ⟨d,some ⟨(U.val.erase (matchingPivot U).val).erase v,
          erased_card U v h.1 h.2.ne.symm⟩⟩
      else ⟨d,none⟩

@[simp] theorem matchingChild_active {b d : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]
    (U : {U : Finset (Fin (b+1)) // U.card=2*(d+1)}) (v : Fin (b+1)) :
    matchingChild G ⟨d+1,some U⟩ v =
      if h : v ∈ U.val ∧ G.Adj (matchingPivot U).val v then
        ⟨d,some ⟨(U.val.erase (matchingPivot U).val).erase v,
          erased_card U v h.1 h.2.ne.symm⟩⟩
      else ⟨d,none⟩ := rfl

theorem matchingChild_rank {b : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]
    (s : MatchingState b) (v : Fin (b+1)) (hr : 0 < matchingRank s) :
    matchingRank (matchingChild G s v)+1=matchingRank s := by
  rcases s with ⟨d,U⟩
  cases d with
  | zero => exact False.elim (Nat.lt_irrefl 0 hr)
  | succ d =>
    cases U with
    | none => rfl
    | some U => rw [matchingChild_active]; split_ifs <;> rfl

/-- For retained partners, the residual count is the exact edge fiber. -/
theorem matchingChild_count_retained {b d : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]
    (U : {U : Finset (Fin (b+1)) // U.card=2*(d+1)}) (v : U.val) :
    matchingStateCount G (matchingChild G ⟨d+1,some U⟩ v.val) =
      matchingChildCount (G.induce (U.val : Set (Fin (b+1)))) (matchingPivot U) v := by
  classical
  by_cases ha : G.Adj (matchingPivot U).val v.val
  · rw [matchingChild_active, dif_pos ⟨v.property,ha⟩]
    change perfectMatchingCount _ = matchingChildCount _ _ _
    rw [matchingChildCount, if_pos (show (G.induce (U.val : Set (Fin (b+1)))).Adj (matchingPivot U) v from ha)]
    exact (perfectMatchingCount_congr (erasePairIso G U.val (matchingPivot U) v)).symm
  · rw [matchingChild_active, dif_neg (by simp [ha])]
    change 0 = matchingChildCount _ _ _
    rw [matchingChildCount, if_neg (show ¬(G.induce (U.val : Set (Fin (b+1)))).Adj (matchingPivot U) v from ha)]

theorem matchingChild_count_outside {b d : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]
    (U : {U : Finset (Fin (b+1)) // U.card=2*(d+1)}) (v : Fin (b+1)) (hv : v ∉ U.val) :
    matchingStateCount G (matchingChild G ⟨d+1,some U⟩ v)=0 := by
  rw [matchingChild_active, dif_neg (by simp [hv])]
  rfl

theorem matchingState_recurrence {b : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]
    (s : MatchingState b) (hr : 0 < matchingRank s) :
    matchingStateCount G s = ∑ v, matchingStateCount G (matchingChild G s v) := by
  classical
  rcases s with ⟨d,U⟩
  cases d with
  | zero => exact False.elim (Nat.lt_irrefl 0 hr)
  | succ d =>
    cases U with
    | none => simp [matchingStateCount, matchingChild]
    | some U =>
      change perfectMatchingCount (G.induce (U.val : Set (Fin (b+1)))) = _
      rw [matching_count_sum_all_partners _ (matchingPivot U)]
      simp_rw [← matchingChild_count_retained G U]
      rw [Finset.sum_coe_sort U.val (fun v => matchingStateCount G (matchingChild G ⟨d+1,some U⟩ v))]
      apply Finset.sum_subset (Finset.subset_univ _)
      intro v _ hv
      exact matchingChild_count_outside G U v hv

/-- A matching-specific self-reduction instance, constructed from exact partner
bijections and actual deletion code. Its recurrence is not supplied as a certificate. -/
noncomputable def matchingReduction {b : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj] :
    CountReduction (MatchingState b) b where
  count := matchingStateCount G
  rank := matchingRank
  child := matchingChild G
  leaf_count := matchingState_leaf G
  child_rank := matchingChild_rank G
  recurrence := matchingState_recurrence G

end HiddenCircuits.Approximation.SelfReduction
