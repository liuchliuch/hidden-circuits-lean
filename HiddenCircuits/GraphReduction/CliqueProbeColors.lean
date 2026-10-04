import HiddenCircuits.GraphReduction.CliqueProbeFibers
import HiddenCircuits.GraphReduction.CliqueProbeExtensionCount
import HiddenCircuits.GraphReduction.CliqueMatchingCount

/-! Even color classes are forced by actual clique-probe matchings at every even sample. -/
namespace HiddenCircuits.GraphReduction
variable {V I : Type*} [Fintype V] [Fintype I]

abbrev CliqueFiber (c : V → Option I) (i : Option I) := {v // c v=i}

noncomputable instance cliqueFiberFintype (c : V → Option I) (i : Option I) :
    Fintype (CliqueFiber c i) := by
  classical
  unfold CliqueFiber
  infer_instance
noncomputable instance cliqueAssignmentsFintype (A : I → V → Prop) : Fintype (CliqueAssignments A) := by
  classical
  unfold CliqueAssignments
  infer_instance
noncomputable instance cliqueBlocksFintype (G : SimpleGraph V) (A : I → V → Prop) (s : ℕ)
    (c : CliqueAssignments A) : Fintype (CliqueBlocks G A s c) := by
  classical
  unfold CliqueBlocks
  infer_instance

def EvenCliqueColors (A : I → V → Prop) :=
  {c : CliqueAssignments A // ∀ i, Even (Fintype.card (CliqueFiber c.val (some i)))}

noncomputable instance evenCliqueColorsFintype (A : I → V → Prop) : Fintype (EvenCliqueColors A) := by
  classical
  unfold EvenCliqueColors
  infer_instance

/-- Half of the number of original vertices assigned to one probe. -/
noncomputable def cliqueHalf {A : I → V → Prop} (c : EvenCliqueColors A) (i : I) : ℕ :=
  Fintype.card (CliqueFiber c.val.val (some i))/2

 theorem cliqueHalf_spec {A : I → V → Prop} (c : EvenCliqueColors A) (i : I) :
    Fintype.card (CliqueFiber c.val.val (some i))=2*cliqueHalf c i := by
  obtain ⟨a,ha⟩ := c.property i
  unfold cliqueHalf
  omega

 theorem cliqueBlocks_even {G : SimpleGraph V} {A : I → V → Prop} {t : ℕ}
    {c : CliqueAssignments A} (b : CliqueBlocks G A (2*t) c) :
    ∀ i, Even (Fintype.card (CliqueFiber c.val (some i))) := by
  intro i
  exact cliqueExtension_even (b.2 i) (by simp only [Fintype.card_fin]; exact ⟨t,by omega⟩)

/-- Parity is inferred from each genuine local matching at size 2t. -/
def evenCliqueBlocksEquiv (G : SimpleGraph V) (A : I → V → Prop) (t : ℕ) :
    (Σ c : CliqueAssignments A, CliqueBlocks G A (2*t) c) ≃
      Σ c : EvenCliqueColors A, CliqueBlocks G A (2*t) c.val where
  toFun d := ⟨⟨d.1,cliqueBlocks_even d.2⟩,d.2⟩
  invFun d := ⟨d.1.val,d.2⟩
  left_inv d := rfl
  right_inv d := rfl

noncomputable def cliquePerfectEvenBlocksEquiv (G : SimpleGraph V) (A : I → V → Prop) (t : ℕ) :
    PerfectMatching (cliqueProbeGraph G A (2*t)) ≃
      Σ c : EvenCliqueColors A, CliqueBlocks G A (2*t) c.val :=
  (cliquePerfectBlocksEquiv G A (2*t)).trans (evenCliqueBlocksEquiv G A t)

end HiddenCircuits.GraphReduction
