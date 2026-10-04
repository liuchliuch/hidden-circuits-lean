import HiddenCircuits.GraphReduction.CliqueProbeColors
import HiddenCircuits.GraphReduction.CliqueProbeFactor

/-! The actual clique-probe graph count, including overlapping attachments and all even sizes. -/
namespace HiddenCircuits.GraphReduction
open scoped BigOperators

 theorem cliqueExtension_card_even {X : Type*} [Fintype X] (a t : ℕ)
    (hX : Fintype.card X=2*a) :
    Fintype.card (CliqueExtension X (Fin (2*t))) =
      (2*t).descFactorial (2*a) * oddFactorial (t-a) := by
  classical
  by_cases ha : a≤t
  · rw [cliqueExtension_card_sum]
    have hc (f : X ↪ Fin (2*t)) :
        Fintype.card (PerfectPartner (⊤ : SimpleGraph (CliqueRemainder f))) = oddFactorial (t-a) := by
      apply completePartner_card_even
      rw [cliqueRemainder_card,Fintype.card_fin,hX]
      omega
    simp_rw [hc]
    simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,Fintype.card_embedding_eq,Fintype.card_fin,hX]
  · rw [cliqueExtension_card_insufficient (by rw [Fintype.card_fin,hX]; omega),
      Nat.descFactorial_eq_zero_iff_lt.mpr (by omega),zero_mul]

 theorem cliqueExtension_count_factor {X : Type*} [Fintype X] (a t : ℕ)
    (hX : Fintype.card X=2*a) :
    Fintype.card (CliqueExtension X (Fin (2*t))) =
      (2^a * t.descFactorial a) * oddFactorial t := by
  rw [cliqueExtension_card_even a t hX,cliqueProbe_factor_nat]
  ring

variable {V I : Type*} [Fintype V] [Fintype I]

 theorem cliqueBlocks_card (G : SimpleGraph V) (A : I → V → Prop) (t : ℕ)
    (c : EvenCliqueColors A) :
    Fintype.card (CliqueBlocks G A (2*t) c.val) =
      perfectMatchingCount (G.induce {v | c.val.val v=none}) *
        (∏ i, 2^(cliqueHalf c i) * t.descFactorial (cliqueHalf c i)) *
          (oddFactorial t)^Fintype.card I := by
  classical
  unfold CliqueBlocks
  rw [Fintype.card_prod,Fintype.card_pi,← perfectMatchingCount_eq_partners]
  simp_rw [cliqueExtension_count_factor _ t (cliqueHalf_spec c _)]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const,Finset.card_univ]
  ring

/-- This is the actual unweighted graph's perfect-matching count, derived from its matching data. -/
theorem cliqueProbeGraph_count (G : SimpleGraph V) (A : I → V → Prop) (t : ℕ) :
    perfectMatchingCount (cliqueProbeGraph G A (2*t)) =
      (∑ c : EvenCliqueColors A, perfectMatchingCount (G.induce {v | c.val.val v=none}) *
        ∏ i, 2^(cliqueHalf c i) * t.descFactorial (cliqueHalf c i)) *
          (oddFactorial t)^Fintype.card I := by
  classical
  rw [perfectMatchingCount,Fintype.card_congr (cliquePerfectEvenBlocksEquiv G A t),Fintype.card_sigma]
  simp_rw [cliqueBlocks_card]
  exact (Finset.sum_mul ..).symm

 theorem cliqueFiber_card_partition (c : V → Option I) :
    Fintype.card (CliqueFiber c none) + ∑ i, Fintype.card (CliqueFiber c (some i)) = Fintype.card V := by
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv c)
  rw [Fintype.card_sigma,Fintype.sum_option] at h
  exact h

 theorem cliqueHalf_sum_le {A : I → V → Prop} (c : EvenCliqueColors A) :
    (∑ i, cliqueHalf c i) ≤ Fintype.card V/2 := by
  have h := cliqueFiber_card_partition c.val.val
  have hh : (∑ i, Fintype.card (CliqueFiber c.val.val (some i))) = 2*(∑ i, cliqueHalf c i) := by
    simp_rw [cliqueHalf_spec,Finset.mul_sum]
  rw [hh] at h
  omega

end HiddenCircuits.GraphReduction
