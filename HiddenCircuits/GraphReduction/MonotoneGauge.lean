import HiddenCircuits.GraphReduction.MonotoneVertices
import HiddenCircuits.GraphReduction.LayerSignProduct
import HiddenCircuits.GraphReduction.BipartiteProbe

/-! The concrete Section 9 probe cancellation and matching-independent endpoint sign. -/
namespace HiddenCircuits.GraphReduction
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The common retained-track predicate in even layer r. -/
def retainedTrack {p h : ℕ} (S T : State (2*p) p) (r : Fin (h+1)) (x : Fin (2*p)) : Prop :=
  (r.val=0 → x∈S.val) ∧ (r.val=h → x∉T.val)

 theorem retainedTrack_first_card {p h : ℕ} (hh : 0<h) (S T : State (2*p) p) :
    Fintype.card {x // retainedTrack S T (0 : Fin (h+1)) x} = p := by
  classical
  let e : {x // retainedTrack S T (0 : Fin (h+1)) x} ≃ S.val :=
    Equiv.subtypeEquivRight (fun x => by simp [retainedTrack,show 0≠h by omega])
  rw [Fintype.card_congr e,Fintype.card_coe,S.property]

 theorem retainedTrack_last_card {p h : ℕ} (hh : 0<h) (S T : State (2*p) p) :
    Fintype.card {x // retainedTrack S T (Fin.last h) x} = p := by
  classical
  let e : {x // retainedTrack S T (Fin.last h) x} ≃ T.halfComplement.val :=
    Equiv.subtypeEquivRight (fun x => by
      simp [retainedTrack,show h≠0 by omega,State.halfComplement_val])
  rw [Fintype.card_congr e,Fintype.card_coe,T.halfComplement.property]

 theorem retainedTrack_middle_card {p h : ℕ} (S T : State (2*p) p)
    (r : Fin (h+1)) (hr0 : r.val≠0) (hrh : r.val≠h) :
    Fintype.card {x // retainedTrack S T r x}=2*p := by
  classical
  let e : {x // retainedTrack S T r x} ≃ Fin (2*p) :=
    { toFun := Subtype.val
      invFun x := ⟨x,by simp [retainedTrack,hr0,hrh]⟩
      left_inv x := rfl
      right_inv x := rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

/-- Exactly the sign stated in the paper, including both boundary restrictions. -/
theorem monotone_endpoint_sign {p h : ℕ} (hh : 0<h) (S T : State (2*p) p) :
    (∏ x : RetainedEven p h S T, (-1 : ℚ)^x.val.1.val) *
      (∏ y : OddVertex (2*p) h, (-1 : ℚ)^y.1.val) = (-1 : ℚ)^(p*h) := by
  rw [oddLayer_sign_product,mul_one]
  calc
    (∏ x : RetainedEven p h S T, (-1 : ℚ)^x.val.1.val) =
        ∏ v : {v : Fin (h+1) × Fin (2*p) // retainedTrack S T v.1 v.2}, (-1 : ℚ)^v.val.1.val :=
      by
        apply Finset.prod_congr
        · ext x; simp
        · intro x _; rfl
    _ = _ := retainedEven_sign_product p h (retainedTrack S T)
      (retainedTrack_last_card hh S T) (retainedTrack_middle_card S T)

/-- Only the one probe attached to the odd endpoint contributes to a possible second cut. -/
theorem monotone_attachment_sum {n h : ℕ} (x : EvenVertex n h) (y : OddVertex n h) :
    (∑ r : Fin h, if evenAttachment r x ∧ oddAttachment r y then (1 : ℚ) else 0) =
      if x.1.val=y.1.val+1 then 1 else 0 := by
  classical
  rw [Finset.sum_eq_single y.1]
  · simp [evenAttachment,oddAttachment]
  · intro r _ hr
    simp [oddAttachment,Ne.symm hr]
  · simp

/-- Subtracting the all-ones second-cut rectangle is exactly an endpoint-sign gauge. -/
theorem monotone_probeWeight {p h : ℕ} (pairs : Fin h → CutPair p)
    (x : EvenVertex (2*p) h) (y : OddVertex (2*p) h) :
    probeWeight (queryRelation pairs) evenAttachment oddAttachment x y =
      (-1 : ℚ)^x.1.val * edgeIndicator (targetRelation pairs) x y * (-1 : ℚ)^y.1.val := by
  classical
  rw [probeWeight,monotone_attachment_sum]
  by_cases hf : x.1.val=y.1.val
  · by_cases he : (pairs y.1).first x.2 y.2=1
    · simp [queryRelation,targetRelation,edgeIndicator,hf,he,pairedLayer_first_sign]
    · simp [queryRelation,targetRelation,edgeIndicator,hf,he]
  · by_cases hs : x.1.val=y.1.val+1
    · by_cases he : (pairs y.1).second y.2 x.2=1
      · simp [queryRelation,targetRelation,edgeIndicator,hs,he,pairedLayer_second_sign]
      · simp [queryRelation,targetRelation,edgeIndicator,hs,he]
    · simp [queryRelation,targetRelation,edgeIndicator,hf,hs]

 theorem retained_monotone_probeWeight {p h : ℕ} (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (x : RetainedEven p h S T) (y : OddVertex (2*p) h) :
    probeWeight (retainedQueryRelation pairs S T) (retainedEvenAttachment S T) oddAttachment x y =
      (-1 : ℚ)^x.val.1.val * edgeIndicator (retainedTargetRelation pairs S T) x y *
        (-1 : ℚ)^y.1.val := monotone_probeWeight pairs x.val y

/-- Exact Section 9 cancellation, already stated for actual retained simple-unweighted graphs. -/
theorem monotone_probe_cancellation {p h : ℕ} (hh : 0<h) (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) :
    (probePolynomial (retainedQueryRelation pairs S T) (retainedEvenAttachment S T) oddAttachment).eval (-1) =
      (-1 : ℚ)^(p*h) * (perfectMatchingCount (cutGraph (retainedTargetRelation pairs S T)) : ℚ) := by
  rw [bipartiteProbe_cancellation]
  have hw : probeWeight (retainedQueryRelation pairs S T) (retainedEvenAttachment S T) oddAttachment =
      (fun x y => (-1 : ℚ)^x.val.1.val * edgeIndicator (retainedTargetRelation pairs S T) x y *
        (-1 : ℚ)^y.1.val) := by
    funext x y
    exact retained_monotone_probeWeight pairs S T x y
  rw [hw,weightedBipartiteCount_signed_graph,monotone_endpoint_sign hh]

end HiddenCircuits.GraphReduction
