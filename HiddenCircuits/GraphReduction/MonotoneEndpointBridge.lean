import HiddenCircuits.GraphReduction.QueryRepresentations
import HiddenCircuits.Approximation.MonotoneStart
namespace HiddenCircuits.GraphReduction
open Approximation
namespace MonotoneOrdering
variable {X Y : Type} [Fintype X] [Fintype Y] {R : X → Y → Prop}
def endpoints (O : MonotoneOrdering R) (h : Fintype.card Y=Fintype.card X) : MonotoneEndpoints (Fintype.card X) where
  lo := O.lo
  hi := O.hi
  lo_mono := O.lo_mono
  hi_mono := O.hi_mono
  lo_le_hi := O.lo_le_hi
  hi_le i := (O.hi_le i).trans_eq h
def balancedColumns (O : MonotoneOrdering R) (h : Fintype.card Y=Fintype.card X) : Fin (Fintype.card X) ≃ Y :=
  (finCongr h.symm).trans O.columns
lemma balanced_neighborhood (O : MonotoneOrdering R) (h : Fintype.card Y=Fintype.card X)
    (i j : Fin (Fintype.card X)) :
    R (O.rows i) (O.balancedColumns h j) ↔ O.lo i ≤ j.val ∧ j.val < O.hi i := by
  exact O.neighborhood i (Fin.cast h.symm j)
lemma permutation_admissible (O : MonotoneOrdering R) (h : Fintype.card Y=Fintype.card X)
    (e : X ≃ Y) :
    (∀x,R x (e x)) ↔ (O.endpoints h).Admissible ((O.rows.symm.equivCongr (O.balancedColumns h).symm) e) := by
  constructor
  · intro he i
    have hh := (O.balanced_neighborhood h i ((O.balancedColumns h).symm (e (O.rows i)))).mp (by simpa using he (O.rows i))
    exact hh
  · intro he x
    have hh := (O.balanced_neighborhood h (O.rows.symm x) ((O.balancedColumns h).symm (e x))).mpr (by simpa using he (O.rows.symm x))
    simpa using hh
noncomputable def cutBijectionEquiv (O : MonotoneOrdering R) (h : Fintype.card Y=Fintype.card X) :
    CutBijection R ≃ (O.endpoints h).Permutations :=
  Equiv.subtypeEquiv (O.rows.symm.equivCongr (O.balancedColumns h).symm) (O.permutation_admissible h)
noncomputable def matchingEquiv (O : MonotoneOrdering R) (h : Fintype.card Y=Fintype.card X) :
    PerfectMatching (cutGraph R) ≃ (O.endpoints h).Permutations :=
  (cutPerfectMatchingEquiv R).trans (O.cutBijectionEquiv h)
theorem count_eq (O : MonotoneOrdering R) (h : Fintype.card Y=Fintype.card X) :
    perfectMatchingCount (cutGraph R)=Fintype.card (O.endpoints h).Permutations := by
  classical
  exact Fintype.card_congr (O.matchingEquiv h)
end MonotoneOrdering
lemma monotone_parts_balanced {p h : ℕ} (hh : 0<h) (S T : State (2*p) p) (s : ℕ) :
    Fintype.card (ProbePart (OddVertex (2*p) h) (Fin h) s)=
      Fintype.card (ProbePart (RetainedEven p h S T) (Fin h) s) := by
  simp only [ProbePart,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,
    retainedEven_card hh,oddVertex_card]
  ring
noncomputable def monotoneQueryEndpoints {p h : ℕ} (hh : 0<h) (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (s : ℕ) :
    MonotoneEndpoints (Fintype.card (ProbePart (RetainedEven p h S T) (Fin h) s)) :=
  (monotoneQueryOrdering pairs S T s).endpoints (monotone_parts_balanced hh S T s)
theorem monotoneQueryEndpoints_count {p h : ℕ} (hh : 0<h) (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (s : ℕ) :
    perfectMatchingCount (monotoneGraphInput pairs S T s).2.graph=
      Fintype.card (monotoneQueryEndpoints hh pairs S T s).Permutations := by
  rw [monotoneGraphInput_count]
  exact (monotoneQueryOrdering pairs S T s).count_eq (monotone_parts_balanced hh S T s)
end HiddenCircuits.GraphReduction
