import HiddenCircuits.Approximation.Initialization.MatchingExtraction
import HiddenCircuits.Approximation.Initialization.PartialPartners

/-! An accumulator-form matching initializer suitable for a literal iterative
machine. Its failure event is exactly the already bounded recursive extractor's
failure event. Successful arrays are proved genuine graph perfect partners. -/
namespace HiddenCircuits.Approximation.Initialization.ForwardExtraction
open SelfReduction ResidualTest

variable {b : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]

def pivot : MatchingState b → Fin (b+1)
  | ⟨0,_⟩ => 0
  | ⟨d+1,none⟩ => 0
  | ⟨d+1,some U⟩ => (matchingPivot U).val

def leaf (s : MatchingState b) (π : Equiv.Perm (Fin (b+1))) : Option (Equiv.Perm (Fin (b+1))) :=
  match s with
  | ⟨0,some _⟩ => some π
  | _ => none

noncomputable def run (k : ℕ) : (d : ℕ) → MatchingState b →
    (Fin d → CoinTape (bits b k)) → Equiv.Perm (Fin (b+1)) → Option (Equiv.Perm (Fin (b+1)))
  | 0,s,_,π => leaf s π
  | d+1,s,r,π =>
      match MatchingExtraction.select G k s (r 0) with
      | none => none
      | some v => run k d (matchingChild G s v) (fun i => r i.succ)
          (MonotoneEndpoints.transpose π (pivot s) v)

theorem run_none_iff (k d : ℕ) (s : MatchingState b) (r : Fin d → CoinTape (bits b k))
    (π : Equiv.Perm (Fin (b+1))) :
    run G k d s r π=none ↔ MatchingExtraction.run G k d s r=none := by
  induction d generalizing s π with
  | zero =>
    rcases s with ⟨e,U⟩
    cases e <;> cases U <;> simp [run,leaf,MatchingExtraction.run,MatchingExtraction.leaf]
  | succ d ih =>
    cases hs : MatchingExtraction.select G k s (r 0) with
    | none => simp [run,MatchingExtraction.run,hs]
    | some v =>
      simp only [run,MatchingExtraction.run,hs,Option.map_eq_none_iff]
      exact ih _ _ _

/-- Forward row swaps establish the actual matching invariant; no output
matching or precomputed certificate is an input to the algorithm. -/
theorem run_valid (k d : ℕ) (U : {U : Finset (Fin (b+1)) // U.card=2*d})
    (r : Fin d → CoinTape (bits b k)) (π ρ : Equiv.Perm (Fin (b+1)))
    (hπ : PartialPartners.Valid G U.val π) (hr : run G k d ⟨d,some U⟩ r π=some ρ) :
    PartialPartners.Valid G ∅ ρ := by
  induction d generalizing π ρ with
  | zero =>
    have hU : U.val=∅ := Finset.card_eq_zero.mp (by simpa using U.property)
    have he : π=ρ := by simpa [run,leaf] using hr
    simpa [←he,hU] using hπ
  | succ d ih =>
    cases hs : MatchingExtraction.select G k ⟨d+1,some U⟩ (r 0) with
    | none => simp [run,hs] at hr
    | some v =>
      have hp := MatchingExtraction.select_sound G k ⟨d+1,some U⟩ (r 0) hs
      have hadj : v∈U.val ∧ G.Adj (matchingPivot U).val v := by
        by_contra h
        rw [matchingChild_active,dif_neg h] at hp
        exact Nat.lt_irrefl 0 hp
      let V : {U : Finset (Fin (b+1)) // U.card=2*d} :=
        ⟨(U.val.erase (matchingPivot U).val).erase v,erased_card U v hadj.1 hadj.2.ne.symm⟩
      have hc : matchingChild G ⟨d+1,some U⟩ v=⟨d,some V⟩ := by
        rw [matchingChild_active,dif_pos hadj]
      have hi := PartialPartners.add_pair hπ (matchingPivot U).val v (matchingPivot U).property hadj.1 hadj.2
      have hh : run G k d ⟨d,some V⟩ (fun i => r i.succ)
          (MonotoneEndpoints.transpose π (matchingPivot U).val v)=some ρ := by
        simpa only [run,hs,hc,pivot] using hr
      exact ih V _ _ ρ hi hh

theorem run_failure (k d : ℕ) (s : MatchingState b)
    (hs : 0 < matchingStateCount G s) (hr : matchingRank s=d) (π : Equiv.Perm (Fin (b+1))) :
    probability (fun r => run G k d s r π=none)≤(d:ℚ)/(2^k:ℚ) := by
  simpa only [run_none_iff] using MatchingExtraction.run_failure G k d s hs hr

end HiddenCircuits.Approximation.Initialization.ForwardExtraction
