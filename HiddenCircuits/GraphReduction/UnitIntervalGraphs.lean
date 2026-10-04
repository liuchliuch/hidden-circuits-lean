import HiddenCircuits.GraphReduction.CliqueProbeGraph
import HiddenCircuits.GraphReduction.MonotoneVertices

/-! Actual original and query graphs of the Section 10 equal-length construction. -/
namespace HiddenCircuits.GraphReduction

/-- Retained boundary original vertices, with the same layer and track labels as Section 9. -/
abbrev UnitOriginalVertex (p h : ℕ) (S T : State (2*p) p) :=
  RetainedEven p h S T ⊕ OddVertex (2*p) h

/-- Complement only the first cut in each pair; retain the actual second cut. -/
def unitIntervalCrossRelation {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p)
    (x : RetainedEven p h S T) (y : OddVertex (2*p) h) : Prop :=
  (x.val.1.val=y.1.val ∧ (pairs y.1).first x.val.2 y.2≠1) ∨
    (x.val.1.val=y.1.val+1 ∧ (pairs y.1).second y.2 x.val.2=1)

/-- Every layer is a clique; there are exactly the prescribed consecutive cuts. -/
def unitIntervalOriginalGraph {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) :
    SimpleGraph (UnitOriginalVertex p h S T) where
  Adj
    | .inl x, .inl y => x.val.1=y.val.1 ∧ x.val.2≠y.val.2
    | .inr x, .inr y => x.1=y.1 ∧ x.2≠y.2
    | .inl x, .inr y => unitIntervalCrossRelation pairs S T x y
    | .inr y, .inl x => unitIntervalCrossRelation pairs S T x y
  symm := by
    intro x y
    cases x <;> cases y
    · exact fun h => ⟨h.1.symm,h.2.symm⟩
    · exact id
    · exact id
    · exact fun h => ⟨h.1.symm,h.2.symm⟩
  loopless := ⟨by intro v; cases v <;> simp⟩

/-- Probe r sees exactly original layers 2r and 2r+1, with no odd layer after the final even layer. -/
def unitIntervalAttachment {p h : ℕ} (S T : State (2*p) p) (r : Fin (h+1)) :
    UnitOriginalVertex p h S T → Prop
  | .inl x => x.val.1=r
  | .inr y => y.1.castSucc=r

/-- The exact simple-unweighted graph submitted at even probe size s. -/
def unitIntervalQueryGraph {p h : ℕ} (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (s : ℕ) :
    SimpleGraph (UnitOriginalVertex p h S T ⊕ (Fin (h+1) × Fin s)) :=
  cliqueProbeGraph (unitIntervalOriginalGraph pairs S T) (unitIntervalAttachment S T) s

/-- Literal layer numbers used by the equal-length interval representation. -/
def unitOriginalLayer {p h : ℕ} {S T : State (2*p) p} : UnitOriginalVertex p h S T → ℤ
  | .inl x => 2*(x.val.1.val : ℤ)
  | .inr y => 2*(y.1.val : ℤ)+1

/-- Literal track labels; first and last layers retain precisely the boundary states. -/
def unitOriginalTrack {p h : ℕ} {S T : State (2*p) p} : UnitOriginalVertex p h S T → Fin (2*p)
  | .inl x => x.val.2
  | .inr y => y.2

/-- Endpoint signs flipping exactly the first cuts and preserving all second cuts. -/
def unitEndpointSign {p h : ℕ} {S T : State (2*p) p} : UnitOriginalVertex p h S T → ℚ
  | .inl x => (-1)^x.val.1.val
  | .inr y => (-1)^(y.1.val+1)

end HiddenCircuits.GraphReduction
