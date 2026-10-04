import HiddenCircuits.Approximation.SelfReduction.SoundZero

/-! A positive empirical count itself witnesses a legal nonempty residual.
This deterministic invariant holds even when statistical accuracy fails. -/
namespace HiddenCircuits.Approximation.SelfReduction

 theorem naturalAmplifiedCount_positive {α : Type*} (E : α → Prop) [DecidablePred E]
    (T k : ℕ) (r : StageTape α T k) (h : 0 < naturalAmplifiedCount E T k r) :
    ∃ a, E a := by
  unfold naturalAmplifiedCount eventCount at h
  obtain ⟨j,hj⟩ := Finset.card_pos.mp h
  exact ⟨_,(Finset.mem_filter.mp hj).2⟩

/-- Every sampled partner comes from an actual complete matching, hence fixing
that partner leaves at least one completion after real vertex-pair deletion. -/
theorem matchingBranchSampler_child_positive {b : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]
    (m : ℕ) (sample : ResidualSampler G m) (s : MatchingState b) (a : CoinTape m) (v : Fin (b+1))
    (h : matchingBranchSampler G m sample s a=some v) :
    0 < matchingStateCount G (matchingChild G s v) := by
  classical
  rcases s with ⟨d,U⟩
  cases d with
  | zero => simp [matchingBranchSampler] at h
  | succ d =>
    cases U with
    | none => simp [matchingBranchSampler] at h
    | some U =>
      cases hs : sample (d+1) U a with
      | none => simp [matchingBranchSampler,hs] at h
      | some p =>
        have hv : (p.val (matchingPivot U)).val=v := by simpa [matchingBranchSampler,hs] using h
        have ha := p.property.2 (matchingPivot U)
        have hp : 0 < matchingChildCount (G.induce (U.val : Set (Fin (b+1))))
            (matchingPivot U) (p.val (matchingPivot U)) := by
          rw [matchingChildCount, if_pos ha, perfectMatchingCount_eq_partners]
          exact Fintype.card_pos_iff.mpr ⟨(edgeDeletionEquiv ha) ⟨p,rfl⟩⟩
        rw [← matchingChild_count_retained G U (p.val (matchingPivot U))] at hp
        simpa only [hv] using hp

/-- The actual natural-only chosen branch is sound whenever its observed count
is nonzero, with no mixing or approximation hypothesis. -/
theorem naturalChosenCount_child_positive {b : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]
    (m : ℕ) (sample : ResidualSampler G m) (T k : ℕ) (s : MatchingState b)
    (r : StageTape (CoinTape m) T k)
    (h : 0 < naturalAmplifiedCount
      (fun a => matchingBranchSampler G m sample s a=
        some (naturalSelectedBranch b T k (matchingBranchSampler G m sample) s r)) T k r) :
    0 < matchingStateCount G (matchingChild G s
      (naturalSelectedBranch b T k (matchingBranchSampler G m sample) s r)) := by
  obtain ⟨a,ha⟩ := naturalAmplifiedCount_positive _ T k r h
  exact matchingBranchSampler_child_positive G m sample s a _ ha

/-- Return failure as soon as an observed factor is zero. This avoids subsequent
sampler calls or graph construction on an empty/rejected branch. -/
def shortMatchingCounts {b : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]
    (m : ℕ) (sample : ResidualSampler G m) (T h : ℕ) :
    (d : ℕ) → MatchingState b → (Fin d → StageTape (CoinTape m) T h) → Option (List ℕ)
  | 0, _, _ => some []
  | d+1, s, tapes =>
      let sampler := matchingBranchSampler G m sample
      let j := naturalSelectedBranch b T h sampler s (tapes 0)
      let c := naturalAmplifiedCount (fun a => sampler s a=some j) T h (tapes 0)
      if c=0 then none else
        (shortMatchingCounts G m sample T h d (matchingChild G s j) (fun i => tapes i.succ)).map (c::·)

 theorem shortMatchingCounts_some {b : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]
    (m : ℕ) (sample : ResidualSampler G m) (T h d : ℕ) (s : MatchingState b)
    (tapes : Fin d → StageTape (CoinTape m) T h) (xs : List ℕ)
    (hx : shortMatchingCounts G m sample T h d s tapes=some xs) :
    naturalMatchingCounts G m sample T h d s tapes=xs := by
  induction d generalizing s xs with
  | zero => simpa [shortMatchingCounts,naturalMatchingCounts] using hx
  | succ d ih =>
    simp only [shortMatchingCounts] at hx
    split_ifs at hx with hz
    obtain ⟨ys,hy,hcons⟩ := Option.map_eq_some_iff.mp hx
    subst xs
    simp only [naturalMatchingCounts]
    congr 1
    exact ih _ _ _ hy

 theorem shortMatchingCounts_none {b : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]
    (m : ℕ) (sample : ResidualSampler G m) (T h d : ℕ) (s : MatchingState b)
    (tapes : Fin d → StageTape (CoinTape m) T h)
    (hx : shortMatchingCounts G m sample T h d s tapes=none) :
    (naturalMatchingCounts G m sample T h d s tapes).prod=0 := by
  induction d generalizing s with
  | zero => simp [shortMatchingCounts] at hx
  | succ d ih =>
    simp only [shortMatchingCounts] at hx
    split_ifs at hx with hz
    · simp only [naturalMatchingCounts,List.prod_cons,hz,zero_mul]
    · have ht := Option.map_eq_none_iff.mp hx
      simp only [naturalMatchingCounts,List.prod_cons]
      rw [ih _ _ ht, mul_zero]

/-- Early failure is byte-for-byte the same zero encoding as completing every
remaining factor: it is safe to stop all future sampler calls immediately. -/
def shortMatchingOutput {b : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]
    (m : ℕ) (sample : ResidualSampler G m) (T h d : ℕ) (s : MatchingState b)
    (tapes : Fin d → StageTape (CoinTape m) T h) : Complexity.BitString :=
  match shortMatchingCounts G m sample T h d s tapes with
  | none => encodeRatio 0 0
  | some xs => reciprocalProductOutput (batchSize T) xs

 theorem shortMatchingOutput_eq {b : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]
    (m : ℕ) (sample : ResidualSampler G m) (T h d : ℕ) (s : MatchingState b)
    (tapes : Fin d → StageTape (CoinTape m) T h) :
    shortMatchingOutput G m sample T h d s tapes =
      reciprocalProductOutput (batchSize T) (naturalMatchingCounts G m sample T h d s tapes) := by
  cases hx : shortMatchingCounts G m sample T h d s tapes with
  | none =>
    have hp := shortMatchingCounts_none G m sample T h d s tapes hx
    simp [shortMatchingOutput,hx,reciprocalProductOutput,hp,encodeRatio]
  | some xs =>
    rw [shortMatchingCounts_some G m sample T h d s tapes xs hx]
    simp [shortMatchingOutput,hx]

end HiddenCircuits.Approximation.SelfReduction
