import HiddenCircuits.GraphReduction.CliqueProbeDecomposition
import HiddenCircuits.GraphReduction.CliqueProbeExtension
import HiddenCircuits.GraphReduction.ProbeFibers

/-! The actual undirected color fibers are the residual original matching and one
independent clique extension per probe color. -/
namespace HiddenCircuits.GraphReduction
variable {V I : Type*}

def CliqueAssignments (A : I → V → Prop) :=
  {c : V → Option I // ∀ v i, c v=some i → A i v}

/-- Original vertices carrying no probe color retain exactly their original graph. -/
def cliqueNonePartnerEquiv (G : SimpleGraph V) (A : I → V → Prop) (s : ℕ) (c : V → Option I) :
    PerfectPartner ((cliqueProbeGraph (originalNoneGraph G c) A s).induce
      {v | extendColor c s v=none}) ≃ PerfectPartner (G.induce {v | c v=none}) :=
  perfectPartnerCongr _ _ (probeNoneFiberEquiv c s) (by
    intro x y
    rcases x with ⟨x|⟨i,j⟩,hx⟩ <;> rcases y with ⟨y|⟨k,l⟩,hy⟩
    all_goals simp only [Set.mem_setOf_eq,extendColor,reduceCtorEq] at hx hy
    change (G.Adj x y ∧ c x=none ∧ c y=none) ↔ G.Adj x y
    simp [hx,hy])

/-- Within color i, each assigned original attaches to every vertex of exactly its probe clique. -/
def cliqueSomePartnerEquiv (G : SimpleGraph V) (A : I → V → Prop) (s : ℕ)
    (c : CliqueAssignments A) (i : I) :
    PerfectPartner ((cliqueProbeGraph (originalNoneGraph G c.val) A s).induce
      {v | extendColor c.val s v=some i}) ≃
      CliqueExtension {v // c.val v=some i} (Fin s) :=
  (perfectPartnerCongr (cliqueExtensionGraph {v // c.val v=some i} (Fin s))
    ((cliqueProbeGraph (originalNoneGraph G c.val) A s).induce
      {v | extendColor c.val s v=some i})
    (probeSomeFiberEquiv c.val s i).symm (by
      intro x y
      cases x with
      | inl x =>
        cases y with
        | inl y =>
          change False ↔ G.Adj x.val y.val ∧ c.val x.val=none ∧ c.val y.val=none
          simp [x.property]
        | inr j =>
          change True ↔ A i x.val
          simp [c.property x.val i x.property]
      | inr j =>
        cases y with
        | inl y =>
          change True ↔ A i y.val
          simp [c.property y.val i y.property]
        | inr k => change (j≠k) ↔ i=i ∧ j≠k; simp)).symm

def CliqueBlocks (G : SimpleGraph V) (A : I → V → Prop) (s : ℕ) (c : CliqueAssignments A) :=
  PerfectPartner (G.induce {v | c.val v=none}) ×
    ∀ i, CliqueExtension {v // c.val v=some i} (Fin s)

def cliqueBlocksEquiv (G : SimpleGraph V) (A : I → V → Prop) (s : ℕ) (c : CliqueAssignments A) :
    ColoredPerfectPartner (cliqueProbeGraph (originalNoneGraph G c.val) A s) (extendColor c.val s) ≃
      CliqueBlocks G A s c :=
  (coloredPerfectPartnerEquiv _ _).trans
    (Equiv.piOptionEquivProd.trans (Equiv.prodCongr (cliqueNonePartnerEquiv G A s c.val)
      (Equiv.piCongrRight (cliqueSomePartnerEquiv G A s c))))

 theorem cliqueDecomposition_valid {G : SimpleGraph V} {A : I → V → Prop} {s : ℕ}
    (d : CliqueProbeDecomposition G A s) : ∀ v i, d.1 v=some i → A i v := by
  intro v i h
  apply cliqueAssignment_allowed d.forget v i
  rw [d.assignment_forget]
  exact h

def validCliqueDecompositionEquiv (G : SimpleGraph V) (A : I → V → Prop) (s : ℕ) :
    CliqueProbeDecomposition G A s ≃ Σ c : CliqueAssignments A,
      ColoredPerfectPartner (cliqueProbeGraph (originalNoneGraph G c.val) A s) (extendColor c.val s) where
  toFun d := ⟨⟨d.1,cliqueDecomposition_valid d⟩,d.2⟩
  invFun d := ⟨d.1.val,d.2⟩
  left_inv d := rfl
  right_inv d := rfl

/-- Every actual clique-probe perfect matching is uniquely specified by these independent data. -/
noncomputable def cliquePerfectBlocksEquiv (G : SimpleGraph V) (A : I → V → Prop) (s : ℕ) :
    PerfectMatching (cliqueProbeGraph G A s) ≃ Σ c : CliqueAssignments A, CliqueBlocks G A s c :=
  (cliquePerfectDecompositionEquiv G A s).trans
    ((validCliqueDecompositionEquiv G A s).trans (Equiv.sigmaCongrRight (cliqueBlocksEquiv G A s)))

end HiddenCircuits.GraphReduction
