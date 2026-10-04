import HiddenCircuits.GraphCounting

/-! Actual matching decomposition across two bags with no cross edges. -/
namespace HiddenCircuits.DH
open SimpleGraph
open scoped BigOperators
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

def disjointGraph (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V ⊕ W) where
  Adj
    | .inl v, .inl w => G.Adj v w
    | .inr v, .inr w => H.Adj v w
    | _, _ => False
  symm := by intro x y; cases x <;> cases y <;> simp; exact G.adj_symm; exact H.adj_symm
  loopless := ⟨by intro x; cases x <;> simp⟩

def combinePartner (p : V → Option V) (q : W → Option W) : V ⊕ W → Option (V ⊕ W)
  | .inl v => (p v).map Sum.inl
  | .inr w => (q w).map Sum.inr

def combineMatching (p : EncodedMatching G) (q : EncodedMatching H) :
    EncodedMatching (disjointGraph G H) := by
  refine ⟨combinePartner p.val q.val,?_,?_⟩
  · intro v w h
    cases v with
    | inl v =>
      cases w with
      | inl w =>
        have hv : p.val v = some w := by simpa [combinePartner] using h
        simpa [combinePartner] using congrArg (Option.map (@Sum.inl V W)) (p.property.1 v w hv)
      | inr w => simp [combinePartner] at h
    | inr v =>
      cases w with
      | inl w => simp [combinePartner] at h
      | inr w =>
        have hv : q.val v = some w := by simpa [combinePartner] using h
        simpa [combinePartner] using congrArg (Option.map (@Sum.inr V W)) (q.property.1 v w hv)
  · intro v w h
    cases v with
    | inl v =>
      cases w with
      | inl w => exact p.property.2 v w (by simpa [combinePartner] using h)
      | inr w => simp [combinePartner] at h
    | inr v =>
      cases w with
      | inl w => simp [combinePartner] at h
      | inr w => exact q.property.2 v w (by simpa [combinePartner] using h)

def leftOption : Option (V ⊕ W) → Option V
  | some (.inl v) => some v
  | _ => none

def rightOption : Option (V ⊕ W) → Option W
  | some (.inr w) => some w
  | _ => none

lemma leftOption_some_iff (o : Option (V ⊕ W)) (v : V) :
    leftOption o = some v ↔ o = some (.inl v) := by
  cases o with
  | none => simp [leftOption]
  | some s => cases s <;> simp [leftOption]

lemma rightOption_some_iff (o : Option (V ⊕ W)) (w : W) :
    rightOption o = some w ↔ o = some (.inr w) := by
  cases o with
  | none => simp [rightOption]
  | some s => cases s <;> simp [rightOption]

def leftMatching (p : EncodedMatching (disjointGraph G H)) : EncodedMatching G := by
  refine ⟨fun v => leftOption (p.val (.inl v)),?_,?_⟩
  · intro v w h
    apply (leftOption_some_iff _ _).mpr
    exact p.property.1 _ _ ((leftOption_some_iff _ _).mp h)
  · intro v w h
    exact p.property.2 _ _ ((leftOption_some_iff _ _).mp h)

def rightMatching (p : EncodedMatching (disjointGraph G H)) : EncodedMatching H := by
  refine ⟨fun v => rightOption (p.val (.inr v)),?_,?_⟩
  · intro v w h
    apply (rightOption_some_iff _ _).mpr
    exact p.property.1 _ _ ((rightOption_some_iff _ _).mp h)
  · intro v w h
    exact p.property.2 _ _ ((rightOption_some_iff _ _).mp h)

lemma left_combine (p : EncodedMatching G) (q : EncodedMatching H) :
    leftMatching (combineMatching p q) = p := by
  apply Subtype.ext
  funext v
  change leftOption ((p.val v).map Sum.inl) = p.val v
  cases p.val v <;> rfl

lemma right_combine (p : EncodedMatching G) (q : EncodedMatching H) :
    rightMatching (combineMatching p q) = q := by
  apply Subtype.ext
  funext v
  change rightOption ((q.val v).map Sum.inr) = q.val v
  cases q.val v <;> rfl

lemma combine_restrict (p : EncodedMatching (disjointGraph G H)) :
    combineMatching (leftMatching p) (rightMatching p) = p := by
  apply Subtype.ext
  funext v
  cases v with
  | inl v =>
    change (leftOption (p.val (.inl v))).map Sum.inl = p.val (.inl v)
    cases h : p.val (.inl v) with
    | none => rfl
    | some w =>
      cases w with
      | inl w => rfl
      | inr w => exact (p.property.2 _ _ h).elim
  | inr v =>
    change (rightOption (p.val (.inr v))).map Sum.inr = p.val (.inr v)
    cases h : p.val (.inr v) with
    | none => rfl
    | some w =>
      cases w with
      | inl w => exact (p.property.2 _ _ h).elim
      | inr w => rfl

/-- Restriction and union give an actual bijection of partial matchings. -/
def disjointMatchingEquiv : EncodedMatching (disjointGraph G H) ≃ EncodedMatching G × EncodedMatching H where
  toFun p := (leftMatching p,rightMatching p)
  invFun p := combineMatching p.1 p.2
  left_inv := combine_restrict
  right_inv p := Prod.ext (left_combine p.1 p.2) (right_combine p.1 p.2)

/-- Only active vertices may remain unmatched inside a bag. -/
def Admissible (T : Set V) (p : EncodedMatching G) : Prop :=
  ∀ v, p.val v = none → v ∈ T

noncomputable def uncovered [Fintype V] (p : EncodedMatching G) : ℕ := by
  classical
  exact ∑ v, if p.val v = none then 1 else 0

lemma combine_admissible_iff (T : Set V) (U : Set W)
    (p : EncodedMatching G) (q : EncodedMatching H) :
    Admissible {x | Sum.elim T U x} (combineMatching p q) ↔ Admissible T p ∧ Admissible U q := by
  simp [Admissible,combineMatching,combinePartner,Sum.forall]
  rfl

lemma uncovered_combine [Fintype V] [Fintype W]
    (p : EncodedMatching G) (q : EncodedMatching H) :
    uncovered (combineMatching p q) = uncovered p + uncovered q := by
  classical
  unfold uncovered
  rw [Fintype.sum_sum_type]
  simp [combineMatching,combinePartner]

/-- Exact mathematical boundary state, as actual graph matchings with k exposed vertices. -/
def BagState (G : SimpleGraph V) [Fintype V] (T : Set V) (k : ℕ) :=
  {p : EncodedMatching G // Admissible T p ∧ uncovered p = k}

/-- False-twin decomposition including active-boundary and uncovered-count semantics. -/
noncomputable def falseTwinStateEquiv [Fintype V] [Fintype W]
    (T : Set V) (U : Set W) (k : ℕ) :
    BagState (disjointGraph G H) {x | Sum.elim T U x} k ≃
      {pq : EncodedMatching G × EncodedMatching H //
        Admissible T pq.1 ∧ Admissible U pq.2 ∧ uncovered pq.1 + uncovered pq.2 = k} :=
  disjointMatchingEquiv.subtypeEquiv (by
    intro p
    change (Admissible _ p ∧ uncovered p = k) ↔ _
    have hp := combine_restrict p
    have ha := combine_admissible_iff T U (leftMatching p) (rightMatching p)
    have hc := uncovered_combine (leftMatching p) (rightMatching p)
    rw [hp] at ha hc
    change _ ↔ Admissible T (leftMatching p) ∧ Admissible U (rightMatching p) ∧
      uncovered (leftMatching p) + uncovered (rightMatching p) = k
    rw [ha,hc]
    tauto)

noncomputable instance [Fintype V] (T : Set V) (k : ℕ) : Fintype (BagState G T k) := by
  classical
  unfold BagState
  infer_instance

noncomputable def splitStatePairs [Fintype V] [Fintype W]
    (T : Set V) (U : Set W) (k : ℕ) :
    {pq : EncodedMatching G × EncodedMatching H //
      Admissible T pq.1 ∧ Admissible U pq.2 ∧ uncovered pq.1 + uncovered pq.2 = k} ≃
    (Σ i : Fin (k+1), BagState G T i.val × BagState H U (k-i.val)) where
  toFun pq := ⟨⟨uncovered pq.val.1,by have := pq.property.2.2; omega⟩,
    ⟨pq.val.1,pq.property.1,rfl⟩,⟨pq.val.2,pq.property.2.1,by change uncovered pq.val.2 = k - uncovered pq.val.1; have := pq.property.2.2; omega⟩⟩
  invFun x := ⟨(x.2.1.val,x.2.2.val),x.2.1.property.1,x.2.2.property.1,by
    have h1 := x.2.1.property.2
    have h2 := x.2.2.property.2
    have hi := x.1.isLt
    change uncovered x.2.1.val + uncovered x.2.2.val = k
    omega⟩
  left_inv pq := by apply Subtype.ext; rfl
  right_inv x := by
    rcases x with ⟨⟨i,hi⟩,⟨p,hp⟩,⟨q,hq⟩⟩
    have he := hp.2
    dsimp only at he
    subst i
    rfl

/-- Actual false-twin states decompose into the convolution's individual cardinal fibers. -/
noncomputable def falseTwinConvolutionEquiv [Fintype V] [Fintype W]
    (T : Set V) (U : Set W) (k : ℕ) :
    BagState (disjointGraph G H) {x | Sum.elim T U x} k ≃
      (Σ i : Fin (k+1), BagState G T i.val × BagState H U (k-i.val)) :=
  (falseTwinStateEquiv T U k).trans (splitStatePairs T U k)

/-- The exact false-twin update, with coefficients counting genuine bag matchings. -/
theorem falseTwin_count [Fintype V] [Fintype W]
    (T : Set V) (U : Set W) (k : ℕ) :
    Fintype.card (BagState (disjointGraph G H) {x | Sum.elim T U x} k) =
      ∑ i : Fin (k+1), Fintype.card (BagState G T i.val) * Fintype.card (BagState H U (k-i.val)) := by
  rw [Fintype.card_congr (falseTwinConvolutionEquiv T U k)]
  simp only [Fintype.card_sigma,Fintype.card_prod]

end HiddenCircuits.DH
