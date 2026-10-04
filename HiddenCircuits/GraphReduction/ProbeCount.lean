import HiddenCircuits.GraphReduction.ProbeBlocks
import HiddenCircuits.GraphReduction.ProbePairCount

/-! Exact cardinal arithmetic for arbitrary overlapping bipartite probe attachments. -/
namespace HiddenCircuits.GraphReduction
open scoped BigOperators
variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]

noncomputable instance originalFiberFintype (c : X → Option I) (i) : Fintype (OriginalFiber c i) := by
  classical
  unfold OriginalFiber
  infer_instance

noncomputable instance assignmentsFintype (A : I → X → Prop) (B : I → Y → Prop) :
    Fintype (Assignments A B) := by
  classical
  unfold Assignments
  infer_instance

noncomputable instance originalResidualFintype (R : X → Y → Prop)
    (cd : (X → Option I) × (Y → Option I)) : Fintype (OriginalResidual R cd) := by
  classical
  unfold OriginalResidual
  infer_instance

noncomputable instance probeBlocksFintype (R : X → Y → Prop) (A : I → X → Prop)
    (B : I → Y → Prop) (s : ℕ) (cd : Assignments A B) : Fintype (ProbeBlocks R A B s cd) := by
  classical
  unfold ProbeBlocks
  infer_instance

def BalancedAssignments (cd : (X → Option I) × (Y → Option I)) : Prop :=
  ∀ i, Fintype.card (OriginalFiber cd.1 (some i)) = Fintype.card (OriginalFiber cd.2 (some i))

def BalancedColors (A : I → X → Prop) (B : I → Y → Prop) :=
  {cd : Assignments A B // BalancedAssignments cd.val}

noncomputable instance balancedColorsFintype (A : I → X → Prop) (B : I → Y → Prop) :
    Fintype (BalancedColors A B) := by
  classical
  unfold BalancedColors
  infer_instance

 theorem probeBlocks_balance {R : X → Y → Prop} {A : I → X → Prop} {B : I → Y → Prop}
    {s : ℕ} {cd : Assignments A B} (b : ProbeBlocks R A B s cd) : BalancedAssignments cd.val :=
  fun i => probePairBijection_balance (b.2 i)

/-- Balance is a consequence of an actual matching; it is not imposed on the query graph. -/
def balancedBlocksEquiv (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop) (s : ℕ) :
    (Σ cd : Assignments A B, ProbeBlocks R A B s cd) ≃
      Σ cd : BalancedColors A B, ProbeBlocks R A B s cd.val where
  toFun d := ⟨⟨d.1,probeBlocks_balance d.2⟩,d.2⟩
  invFun d := ⟨d.1.val,d.2⟩
  left_inv d := rfl
  right_inv d := rfl

noncomputable def probePerfectBalancedEquiv (R : X → Y → Prop) (A : I → X → Prop)
    (B : I → Y → Prop) (s : ℕ) :
    PerfectMatching (probeGraph R A B s) ≃
      Σ cd : BalancedColors A B, ProbeBlocks R A B s cd.val :=
  (probePerfectBlocksEquiv R A B s).trans (balancedBlocksEquiv R A B s)

 theorem probeBlocks_card (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop)
    (s : ℕ) (cd : BalancedColors A B) :
    Fintype.card (ProbeBlocks R A B s cd.val) =
      Fintype.card (OriginalResidual R cd.val.val) *
        (∏ i, s.descFactorial (Fintype.card (OriginalFiber cd.val.val.1 (some i)))) *
        s.factorial ^ Fintype.card I := by
  classical
  unfold ProbeBlocks
  rw [Fintype.card_prod,Fintype.card_pi]
  simp_rw [probePairBijection_card (cd.property _),Fintype.card_fin]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const,Finset.card_univ]
  ring

/-- All matching-count factors are derived from the actual perfect-matching bijection. -/
theorem probeGraph_count (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop) (s : ℕ) :
    perfectMatchingCount (probeGraph R A B s) =
      (∑ cd : BalancedColors A B, Fintype.card (OriginalResidual R cd.val.val) *
        ∏ i, s.descFactorial (Fintype.card (OriginalFiber cd.val.val.1 (some i)))) *
      s.factorial ^ Fintype.card I := by
  classical
  rw [perfectMatchingCount,Fintype.card_congr (probePerfectBalancedEquiv R A B s),Fintype.card_sigma]
  simp_rw [probeBlocks_card]
  exact (Finset.sum_mul ..).symm

/-- Color fibers partition original vertices even when their allowed neighborhoods overlap. -/
theorem originalFiber_card_partition (c : X → Option I) :
    Fintype.card (OriginalFiber c none) + ∑ i, Fintype.card (OriginalFiber c (some i)) =
      Fintype.card X := by
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv c)
  rw [Fintype.card_sigma,Fintype.sum_option] at h
  exact h

 theorem assigned_card_le (c : X → Option I) :
    (∑ i, Fintype.card (OriginalFiber c (some i))) ≤ Fintype.card X := by
  have h := originalFiber_card_partition c
  omega

end HiddenCircuits.GraphReduction
