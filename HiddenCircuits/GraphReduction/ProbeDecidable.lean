import HiddenCircuits.GraphReduction.MonotoneVertices

/-! Decidable literal adjacency for every unweighted probe query. -/
namespace HiddenCircuits.GraphReduction
variable {X Y I : Type*}

instance decidableCutGraph (R : X → Y → Prop) [DecidableRel R] :
    DecidableRel (cutGraph R).Adj := by
  intro x y
  cases x <;> cases y <;> dsimp [cutGraph] <;> infer_instance

instance decidableProbeRelation (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop)
    [DecidableEq I] [DecidableRel R] [∀ i, DecidablePred (A i)] [∀ i, DecidablePred (B i)]
    (s : ℕ) : DecidableRel (probeRelation R A B s) := by
  intro x y
  cases x with
  | inl x => cases y <;> dsimp [probeRelation] <;> infer_instance
  | inr x => cases y <;> dsimp [probeRelation] <;> infer_instance

instance decidableProbeGraph (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop)
    [DecidableEq I] [DecidableRel R] [∀ i, DecidablePred (A i)] [∀ i, DecidablePred (B i)]
    (s : ℕ) : DecidableRel (probeGraph R A B s).Adj := decidableCutGraph _

instance decidableEvenAttachment {n h : ℕ} (r : Fin h) :
    DecidablePred (evenAttachment (n:=n) r) := fun _ => inferInstanceAs (Decidable (_=_))
instance decidableOddAttachment {n h : ℕ} (r : Fin h) :
    DecidablePred (oddAttachment (n:=n) r) := fun _ => inferInstanceAs (Decidable (_=_))

instance decidableQueryRelation {p h : ℕ} (pairs : Fin h → CutPair p) :
    DecidableRel (queryRelation pairs) := by
  intro x y
  unfold queryRelation
  infer_instance
instance decidableTargetRelation {p h : ℕ} (pairs : Fin h → CutPair p) :
    DecidableRel (targetRelation pairs) := by
  intro x y
  unfold targetRelation
  infer_instance
instance decidableRetainedQueryRelation {p h : ℕ} (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) : DecidableRel (retainedQueryRelation pairs S T) :=
  fun x y => decidableQueryRelation pairs x.val y
instance decidableRetainedTargetRelation {p h : ℕ} (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) : DecidableRel (retainedTargetRelation pairs S T) :=
  fun x y => decidableTargetRelation pairs x.val y
instance decidableRetainedEvenAttachment {p h : ℕ} (S T : State (2*p) p) (r : Fin h) :
    DecidablePred (retainedEvenAttachment S T r) :=
  fun x => decidableEvenAttachment r x.val

instance decidableMonotoneQueryGraph {p h : ℕ} (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (s : ℕ) : DecidableRel (monotoneQueryGraph pairs S T s).Adj :=
  decidableProbeGraph _ _ _ s

end HiddenCircuits.GraphReduction
