import HiddenCircuits.ExactSampling.DHWeights
import HiddenCircuits.Approximation.SelfReduction.MatchingStates

/-!
# Recursive exact unranking of labeled DH perfect matchings

The recursion uses only the checked binary counts on the literal pair-deleted
matrices. Every choice is the interval split derived in `DHWeights`. The graph
isomorphisms restore the original vertex names when each selected edge is
inserted. There is no enumeration or arbitrary indexing of all matchings.
-/
namespace HiddenCircuits.ExactSampling.DHIndex
open Complexity DH Approximation Approximation.SelfReduction
open Approximation.SelfReduction.Runtime DHWeights
open scoped BigOperators

 def partnerIso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : PerfectPartner G ≃ PerfectPartner H where
  toFun := transportPerfectPartner e
  invFun := transportPerfectPartner e.symm
  left_inv := transportPerfectPartner_inverse e
  right_inv := transportPerfectPartner_inverse e.symm

 def emptyPartner (G : MatrixGraph 0) : PerfectPartner G.graph :=
  ⟨Fin.elim0,by intro v; exact v.elim0,by intro v; exact v.elim0⟩

 theorem empty_count (G : MatrixGraph 0) (hG : DistanceHereditaryGraph G.graph) :
    count ⟨0,G⟩=1 := by rw [count_correct _ hG]; exact perfectMatchingCount_empty_vertices _

 def emptyIndex (G : MatrixGraph 0) (hG : DistanceHereditaryGraph G.graph) :
    Fin (count ⟨0,G⟩) ≃ PerfectPartner G.graph where
  toFun _ := emptyPartner G
  invFun _ := ⟨0,by rw [empty_count G hG]; omega⟩
  left_inv i := by
    apply Fin.ext
    have h := i.isLt
    have hc := empty_count G hG
    change 0=i.val
    omega
  right_inv p := by apply Subtype.ext; funext v; exact v.elim0

 theorem residual_smaller {N : ℕ} (G : MatrixGraph (N+1)) (j : Fin (N+1))
    (ha : G.graph.Adj 0 j) : (GraphResidual.retained j).card<N+1 := by
  have h := GraphResidual.retained_card j ha.ne.symm
  omega

/-- Actual recursive count-based unranking. The mutually inverse rank map is
provided by the same interval decomposition, so every labeled matching occurs
once, with no quotient by graph automorphisms. -/
noncomputable def indexEquiv : (n : ℕ) → (G : MatrixGraph n) →
    (hG : DistanceHereditaryGraph G.graph) → Fin (count ⟨n,G⟩) ≃ PerfectPartner G.graph
  | 0,G,hG => emptyIndex G hG
  | N+1,G,hG =>
    (splitIndex G hG).trans ((Equiv.sigmaCongrRight (fun j =>
      if ha : G.graph.Adj 0 j then
        (finCongr (show weight G j=count ⟨_,GraphResidual.graph G j⟩ by
          simp [weight,show G.edge 0 j=true from ha])).trans
          ((indexEquiv (GraphResidual.retained j).card (GraphResidual.graph G j)
            (residual_hereditary G hG j)).trans
            ((partnerIso (GraphResidual.graphIso G j)).trans (edgeDeletionEquiv ha).symm))
      else
        { toFun := fun x => False.elim (by
            have hx := x.isLt
            have hz : weight G j=0 := by simp [weight,show G.edge 0 j=false from Bool.eq_false_iff.mpr ha]
            omega)
          invFun := fun x => False.elim (ha (by simpa [x.property] using x.val.property.2 0))
          left_inv := fun x => False.elim (by
            have hx := x.isLt
            have hz : weight G j=0 := by simp [weight,show G.edge 0 j=false from Bool.eq_false_iff.mpr ha]
            omega)
          right_inv := fun x => False.elim (ha (by simpa [x.property] using x.val.property.2 0)) })).trans
        (allPartnerFiberEquiv G.graph 0).symm)
termination_by n => n
decreasing_by exact residual_smaller G j ha

/-- The output is always an actual original-labeled perfect matching. -/
noncomputable def unrank {n : ℕ} (G : MatrixGraph n) (hG : DistanceHereditaryGraph G.graph)
    (x : Fin (count ⟨n,G⟩)) : PerfectMatching G.graph :=
  (indexEquiv n G hG x).toMatching

 theorem unrank_bijective {n : ℕ} (G : MatrixGraph n) (hG : DistanceHereditaryGraph G.graph) :
    Function.Bijective (unrank G hG) :=
  ((indexEquiv n G hG).trans (perfectPartnerEquiv G.graph).symm).bijective

/-- Each complete random experiment consists of actual rejected fair-bit
blocks and the uniquely accepted bounded integer. -/
def Experiment {n : ℕ} (G : MatrixGraph n) (t : ℕ) :=
  Rejection.Trace (count ⟨n,G⟩) t × Fin (count ⟨n,G⟩)

noncomputable instance {n : ℕ} (G : MatrixGraph n) (t : ℕ) : Fintype (Experiment G t) := by
  unfold Experiment
  infer_instance

noncomputable def experimentOutput {n : ℕ} (G : MatrixGraph n)
    (hG : DistanceHereditaryGraph G.graph) (t : ℕ) (r : Experiment G t) : PerfectMatching G.graph :=
  unrank G hG r.2

noncomputable def outputFiber {n : ℕ} (G : MatrixGraph n) (hG : DistanceHereditaryGraph G.graph)
    (M : PerfectMatching G.graph) (t : ℕ) :
    {r : Experiment G t // experimentOutput G hG t r=M} ≃ Rejection.Trace (count ⟨n,G⟩) t where
  toFun r := r.val.1
  invFun r := ⟨(r,((indexEquiv n G hG).trans (perfectPartnerEquiv G.graph).symm).symm M),by
    change ((indexEquiv n G hG).trans (perfectPartnerEquiv G.graph).symm)
      (((indexEquiv n G hG).trans (perfectPartnerEquiv G.graph).symm).symm M)=M
    exact Equiv.apply_symm_apply _ M⟩
  left_inv r := by
    apply Subtype.ext
    change (r.val.1,((indexEquiv n G hG).trans (perfectPartnerEquiv G.graph).symm).symm M)=r.val
    apply Prod.ext
    · rfl
    apply (unrank_bijective G hG).1
    exact (Equiv.apply_symm_apply ((indexEquiv n G hG).trans (perfectPartnerEquiv G.graph).symm) M).trans r.property.symm
  right_inv _ := rfl

/-- The law is computed from the cardinality of the actual output fiber of
complete finite experiments, multiplied by the fair-bit cylinder weight. -/
noncomputable def matchingMass {n : ℕ} (G : MatrixGraph n) (hG : DistanceHereditaryGraph G.graph)
    (M : PerfectMatching G.graph) (t : ℕ) : ℝ := by
  classical
  exact (Fintype.card {r : Experiment G t // experimentOutput G hG t r=M} : ℝ) /
    (2^((t+1)*Rejection.width (count ⟨n,G⟩)) : ℝ)

 theorem matchingMass_eq {n : ℕ} (G : MatrixGraph n) (hG : DistanceHereditaryGraph G.graph)
    (M : PerfectMatching G.graph) (t : ℕ) :
    matchingMass G hG M t=Rejection.outcomeMass (count ⟨n,G⟩) t := by
  classical
  unfold matchingMass Rejection.outcomeMass
  have hc := Fintype.card_congr (outputFiber G hG M t)
  exact congrArg (fun k : ℕ => (k : ℝ)/(2^((t+1)*Rejection.width (count ⟨n,G⟩)) : ℝ)) hc

 theorem count_pos_of_matching {n : ℕ} (G : MatrixGraph n) (hG : DistanceHereditaryGraph G.graph)
    (M : PerfectMatching G.graph) : 0<count ⟨n,G⟩ := by
  have x := ((indexEquiv n G hG).trans (perfectPartnerEquiv G.graph).symm).symm M
  exact Nat.zero_lt_of_lt x.isLt

/-- Uniformity is exact and unconditional over all finite fair-bit traces. -/
 theorem exact_uniform {n : ℕ} (G : MatrixGraph n) (hG : DistanceHereditaryGraph G.graph)
    (M : PerfectMatching G.graph) :
    ∑'t,matchingMass G hG M t=1/(perfectMatchingCount G.graph : ℝ) := by
  simp_rw [matchingMass_eq]
  rw [Rejection.outcomeMass_sum (count_pos_of_matching G hG M),count_correct ⟨n,G⟩ hG]

/-- No-instance behavior is an explicit failure; it differs from the unique
successful empty matching. -/
noncomputable def sampleIndex {n : ℕ} (G : MatrixGraph n) (hG : DistanceHereditaryGraph G.graph)
    (x : ℕ) : Option (PerfectMatching G.graph) :=
  if hx : x<count ⟨n,G⟩ then some (unrank G hG ⟨x,hx⟩) else none

 theorem sampleIndex_zero {n : ℕ} (G : MatrixGraph n) (hG : DistanceHereditaryGraph G.graph)
    (h : perfectMatchingCount G.graph=0) (x : ℕ) : sampleIndex G hG x=none := by
  have hc := (count_correct ⟨n,G⟩ hG).trans h
  simp [sampleIndex,hc]

 theorem sampleIndex_empty (G : MatrixGraph 0) (hG : DistanceHereditaryGraph G.graph) :
    sampleIndex G hG 0=some (emptyPartner G).toMatching := by
  simp [sampleIndex,empty_count G hG,unrank,indexEquiv,emptyIndex]

 theorem quasiChains_exact_uniform {n : ℕ} (G : MatrixGraph n) (hG : QuasiChains G.graph)
    (M : PerfectMatching G.graph) :
    ∑'t,matchingMass G (quasiChains_distanceHereditary hG) M t=
      1/(perfectMatchingCount G.graph : ℝ) := exact_uniform G _ M

end HiddenCircuits.ExactSampling.DHIndex
