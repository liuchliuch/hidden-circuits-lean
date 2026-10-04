import HiddenCircuits.GraphReduction.CliqueProbeGraph

/-! Canonical decomposition of actual clique-probe matchings by original vertex colors. -/
namespace HiddenCircuits.GraphReduction
variable {V I : Type*}

/-- In the residual original matching, both endpoints have no probe color. -/
def originalNoneGraph (G : SimpleGraph V) (c : V → Option I) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ c v=none ∧ c w=none
  symm := by intro v w h; exact ⟨h.1.symm,h.2.2,h.2.1⟩
  loopless := ⟨by intro v h; exact G.loopless.irrefl v h.1⟩

def CliqueProbeDecomposition (G : SimpleGraph V) (A : I → V → Prop) (s : ℕ) :=
  Σ c : V → Option I,
    ColoredPerfectPartner (cliqueProbeGraph (originalNoneGraph G c) A s) (extendColor c s)

namespace CliqueProbeDecomposition
variable {G : SimpleGraph V} {A : I → V → Prop} {s : ℕ}

def forget (d : CliqueProbeDecomposition G A s) : PerfectPartner (cliqueProbeGraph G A s) :=
  ⟨d.2.val.val,d.2.val.property.1,by
    intro v
    have h := d.2.val.property.2 v
    cases v with
    | inl v =>
      cases he : d.2.val.val (.inl v) with
      | inl w => rw [he] at h; exact h.1
      | inr w => rw [he] at h; exact h
    | inr v => cases he : d.2.val.val (.inr v) <;> rw [he] at h <;> exact h⟩

 theorem assignment_forget (d : CliqueProbeDecomposition G A s) : cliqueAssignment d.forget=d.1 := by
  funext v
  have hp := d.2.property (.inl v)
  have ha := d.2.val.property.2 (.inl v)
  change extendColor d.1 s (d.forget.val (.inl v)) = d.1 v at hp
  change (cliqueProbeGraph (originalNoneGraph G d.1) A s).Adj (.inl v)
    (d.forget.val (.inl v)) at ha
  unfold cliqueAssignment
  cases he : d.forget.val (.inl v) with
  | inl w => rw [he] at ha; exact ha.2.1.symm
  | inr w => rw [he] at hp; exact hp

 theorem forget_injective : Function.Injective (forget (G:=G) (A:=A) (s:=s)) := by
  rintro ⟨c,p⟩ ⟨d,q⟩ he
  have hc := congrArg cliqueAssignment he
  rw [assignment_forget,assignment_forget] at hc
  dsimp at hc
  subst d
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun p : PerfectPartner (cliqueProbeGraph G A s) => p.val) he
end CliqueProbeDecomposition

/-- Extract each original vertex's actual probe partner label. -/
def decomposeCliqueProbe {G : SimpleGraph V} {A : I → V → Prop} {s : ℕ}
    (p : PerfectPartner (cliqueProbeGraph G A s)) : CliqueProbeDecomposition G A s := by
  refine ⟨cliqueAssignment p,⟨⟨p.val,p.property.1,?_⟩,cliqueAssignment_preserved p⟩⟩
  intro v
  have ha := p.property.2 v
  have hi := p.property.1 v
  cases v with
  | inl v =>
    cases he : p.val (.inl v) with
    | inl w =>
      rw [he] at ha hi
      exact ⟨ha,by simp [cliqueAssignment,he],by simp [cliqueAssignment,hi]⟩
    | inr w => rw [he] at ha; exact ha
  | inr v => cases he : p.val (.inr v) <;> rw [he] at ha <;> exact ha

def cliqueProbeDecompositionEquiv (G : SimpleGraph V) (A : I → V → Prop) (s : ℕ) :
    PerfectPartner (cliqueProbeGraph G A s) ≃ CliqueProbeDecomposition G A s where
  toFun := decomposeCliqueProbe
  invFun := CliqueProbeDecomposition.forget
  left_inv p := rfl
  right_inv d := by apply CliqueProbeDecomposition.forget_injective; rfl

/-- A genuine two-sided equivalence with the simple graph's actual perfect matching subgraphs. -/
noncomputable def cliquePerfectDecompositionEquiv (G : SimpleGraph V) (A : I → V → Prop) (s : ℕ) :
    PerfectMatching (cliqueProbeGraph G A s) ≃ CliqueProbeDecomposition G A s :=
  (perfectPartnerEquiv _).trans (cliqueProbeDecompositionEquiv G A s)

end HiddenCircuits.GraphReduction
