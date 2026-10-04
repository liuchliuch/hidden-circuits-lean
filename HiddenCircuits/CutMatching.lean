import HiddenCircuits.PerfectPartners
import HiddenCircuits.PairedTransfers

/-! A genuine one-cut graph and its perfect-matching/permanental-transfer semantics. -/
namespace HiddenCircuits
open SimpleGraph
open scoped BigOperators

/-- The simple bipartite graph with exactly the specified cut edges. -/
def cutGraph {α β : Type*} (R : α → β → Prop) : SimpleGraph (α ⊕ β) where
  Adj
    | .inl a, .inr b => R a b
    | .inr b, .inl a => R a b
    | _, _ => False
  symm := by intro x y; cases x <;> cases y <;> simp
  loopless := ⟨by intro x; cases x <;> simp⟩

/-- A bijection using only actual available cut edges. -/
def CutBijection {α β : Type*} (R : α → β → Prop) := {e : α ≃ β // ∀ a, R a (e a)}

namespace PerfectPartner
variable {α β : Type*} {R : α → β → Prop}

 theorem exists_cutRight (p : PerfectPartner (cutGraph R)) (a : α) :
    ∃ b, p.val (.inl a) = .inr b := by
  have h := p.property.2 (.inl a)
  cases hp : p.val (.inl a) with
  | inl a' => rw [hp] at h; exact h.elim
  | inr b => exact ⟨b,rfl⟩

 theorem exists_cutLeft (p : PerfectPartner (cutGraph R)) (b : β) :
    ∃ a, p.val (.inr b) = .inl a := by
  have h := p.property.2 (.inr b)
  cases hp : p.val (.inr b) with
  | inl a => exact ⟨a,rfl⟩
  | inr b' => rw [hp] at h; exact h.elim

noncomputable def cutRight (p : PerfectPartner (cutGraph R)) (a : α) : β :=
  (p.exists_cutRight a).choose
noncomputable def cutLeft (p : PerfectPartner (cutGraph R)) (b : β) : α :=
  (p.exists_cutLeft b).choose

 theorem cutRight_spec (p : PerfectPartner (cutGraph R)) (a : α) :
    p.val (.inl a) = .inr (p.cutRight a) := (p.exists_cutRight a).choose_spec
 theorem cutLeft_spec (p : PerfectPartner (cutGraph R)) (b : β) :
    p.val (.inr b) = .inl (p.cutLeft b) := (p.exists_cutLeft b).choose_spec

noncomputable def cutEquiv (p : PerfectPartner (cutGraph R)) : α ≃ β where
  toFun := p.cutRight
  invFun := p.cutLeft
  left_inv a := by
    have h := p.property.1 (.inl a)
    rw [p.cutRight_spec,p.cutLeft_spec] at h
    exact Sum.inl.inj h
  right_inv b := by
    have h := p.property.1 (.inr b)
    rw [p.cutLeft_spec,p.cutRight_spec] at h
    exact Sum.inr.inj h

noncomputable def toCutBijection (p : PerfectPartner (cutGraph R)) : CutBijection R :=
  ⟨p.cutEquiv,by
    intro a
    have h := p.property.2 (.inl a)
    rw [p.cutRight_spec] at h
    exact h⟩
end PerfectPartner

namespace CutBijection
variable {α β : Type*} {R : α → β → Prop}

def toPartner (e : CutBijection R) : PerfectPartner (cutGraph R) := by
  refine ⟨(fun x => match x with
    | .inl a => .inr (e.val a)
    | .inr b => .inl (e.val.symm b)),?_,?_⟩
  · intro x
    cases x <;> simp
  · intro x
    cases x with
    | inl a => exact e.property a
    | inr b =>
      change R (e.val.symm b) b
      simpa only [Equiv.apply_symm_apply] using e.property (e.val.symm b)

 theorem toPartner_toCutBijection (e : CutBijection R) : e.toPartner.toCutBijection = e := by
  apply Subtype.ext
  apply Equiv.ext
  intro a
  have h := e.toPartner.cutRight_spec a
  exact (Sum.inr.inj h).symm
end CutBijection

 theorem PerfectPartner.toCutBijection_toPartner {α β : Type*} {R : α → β → Prop}
    (p : PerfectPartner (cutGraph R)) : p.toCutBijection.toPartner = p := by
  apply Subtype.ext
  funext x
  cases x with
  | inl a => exact (p.cutRight_spec a).symm
  | inr b => exact (p.cutLeft_spec b).symm

/-- Restricting a perfect matching to its left-to-right partners is a bijection. -/
noncomputable def cutPerfectMatchingEquiv {α β : Type*} (R : α → β → Prop) :
    PerfectMatching (cutGraph R) ≃ CutBijection R :=
  (perfectPartnerEquiv _).trans
    { toFun := PerfectPartner.toCutBijection
      invFun := CutBijection.toPartner
      left_inv := PerfectPartner.toCutBijection_toPartner
      right_inv := CutBijection.toPartner_toCutBijection }

noncomputable instance {α β : Type*} [Fintype α] [Fintype β] (R : α → β → Prop) :
    Fintype (CutBijection R) := by
  classical
  unfold CutBijection
  infer_instance

 theorem cutPerfectMatchingCount {α β : Type*} [Fintype α] [Fintype β] (R : α → β → Prop) :
    perfectMatchingCount (cutGraph R) = Fintype.card (CutBijection R) :=
  Fintype.card_congr (cutPerfectMatchingEquiv R)

/-- The permanent of a zero-one matrix literally counts its allowed permutations. -/
theorem permanent_indicator_count {α : Type*} [Fintype α] [DecidableEq α]
    (R : α → α → Prop) [DecidableRel R] :
    Matrix.permanent (fun i j => if R i j then (1 : ℚ) else 0) =
      (Fintype.card {σ : Equiv.Perm α // ∀ j, R (σ j) j} : ℚ) := by
  simp only [Matrix.permanent,Fintype.prod_boole,Fintype.card_subtype]
  simp

/-- Inverting the selected permutation gives the literal left-to-right matching bijection. -/
noncomputable def cutPermutationEquiv {α : Type*} (R : α → α → Prop) :
    {σ : Equiv.Perm α // ∀ j, R (σ j) j} ≃ CutBijection R where
  toFun σ := ⟨σ.val.symm,fun i => by simpa using σ.property (σ.val.symm i)⟩
  invFun e := ⟨e.val.symm,fun j => by simpa using e.property (e.val.symm j)⟩
  left_inv σ := by apply Subtype.ext; exact Equiv.symm_symm _
  right_inv e := by apply Subtype.ext; exact Equiv.symm_symm _

/-- Actual simple-unweighted one-cut perfect matchings are counted by the permanent. -/
theorem cutPerfectMatchingCount_eq_permanent {α : Type*} [Fintype α] [DecidableEq α]
    (R : α → α → Prop) [DecidableRel R] :
    (perfectMatchingCount (cutGraph R) : ℚ) =
      Matrix.permanent (fun i j => if R i j then (1 : ℚ) else 0) := by
  rw [cutPerfectMatchingCount,permanent_indicator_count,Fintype.card_congr (cutPermutationEquiv R)]

/-- The graph at one cut retains exactly the input tracks and the complement of the
outgoing state, indexed by their actual increasing track enumerations. -/
def stateCutGraph {p : ℕ} (R : Fin (2*p) → Fin (2*p) → Prop)
    (S T : State (2*p) p) : SimpleGraph (Fin p ⊕ Fin p) :=
  cutGraph (fun i j => R (S.track i) (T.halfComplement.track j))

/-- The first concrete graph-to-transfer identity, including the essential complement. -/
theorem stateCutGraph_count {p : ℕ} (R : Fin (2*p) → Fin (2*p) → Prop) [DecidableRel R]
    (S T : State (2*p) p) :
    (perfectMatchingCount (stateCutGraph R S T) : ℚ) =
      layerTransfer (fun i j => if R i j then (1 : ℚ) else 0) S T := by
  rw [layerTransfer_apply]
  exact cutPerfectMatchingCount_eq_permanent (fun i j => R (S.track i) (T.halfComplement.track j))

end HiddenCircuits
