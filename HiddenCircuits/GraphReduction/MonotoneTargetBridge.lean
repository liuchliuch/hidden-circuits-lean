import HiddenCircuits.GraphReduction.PairedCoordinates
import HiddenCircuits.GraphIsomorphismCount

/-! Exact graph isomorphism from the target's retained even/odd coordinates to the
already verified layered PairEval graph. -/
namespace HiddenCircuits.GraphReduction

 theorem pairVertex_ghost_even {p : ℕ} (w : List (CutPair p)) (S T : State (2*p) p)
    (j : Fin (w.length+1)) (x : Fin (2*p)) :
    Layered.Ghost (pairCuts w) S T (pairVertexEquiv w (.inl (j,x))) ↔
      (j.val=0 ∧ x ∉ S.val) ∨ (j.val=w.length ∧ x ∈ T.val) := by
  rw [Layered.ghost_coordinates]
  simp only [pairVertex_even_layer,pairVertex_even_track,pairCuts_length]
  have h0 : 2*j.val=0 ↔ j.val=0 := by omega
  have hh : 2*j.val=2*w.length ↔ j.val=w.length := by omega
  rw [h0,hh]

 theorem pairVertex_even_retained {p : ℕ} (w : List (CutPair p)) (S T : State (2*p) p)
    (j : Fin (w.length+1)) (x : Fin (2*p)) :
    ¬Layered.Ghost (pairCuts w) S T (pairVertexEquiv w (.inl (j,x))) ↔
      (j.val=0 → x ∈ S.val) ∧ (j.val=w.length → x ∉ T.val) := by
  classical
  rw [pairVertex_ghost_even]
  tauto

 theorem pairVertex_odd_retained {p : ℕ} (w : List (CutPair p)) (S T : State (2*p) p)
    (r : Fin w.length) (x : Fin (2*p)) :
    ¬Layered.Ghost (pairCuts w) S T (pairVertexEquiv w (.inr (r,x))) := by
  rw [Layered.ghost_coordinates]
  simp only [pairVertex_odd_layer,pairVertex_odd_track,pairCuts_length]
  have hr := r.isLt
  omega

/-- Boundary retention as a predicate on the full two-color coordinate space. -/
def RetainEvenOdd {p h : ℕ} (S T : State (2*p) p) :
    EvenVertex (2*p) h ⊕ OddVertex (2*p) h → Prop
  | .inl v => (v.1.val=0 → v.2 ∈ S.val) ∧ (v.1.val=h → v.2 ∉ T.val)
  | .inr _ => True

/-- The separately typed retained color classes are the literal retained full coordinate set. -/
def retainedSumEquiv {p h : ℕ} (S T : State (2*p) p) :
    RetainedEven p h S T ⊕ OddVertex (2*p) h ≃
      {v : EvenVertex (2*p) h ⊕ OddVertex (2*p) h // RetainEvenOdd S T v} where
  toFun
    | .inl v => ⟨.inl v.val,v.property⟩
    | .inr v => ⟨.inr v,True.intro⟩
  invFun
    | ⟨.inl v,hv⟩ => .inl ⟨v,hv⟩
    | ⟨.inr v,_⟩ => .inr v
  left_inv := by intro v; cases v <;> rfl
  right_inv := by rintro ⟨v | v,hv⟩ <;> rfl

 theorem pairVertex_retained_iff {p : ℕ} (w : List (CutPair p)) (S T : State (2*p) p)
    (v : EvenVertex (2*p) w.length ⊕ OddVertex (2*p) w.length) :
    RetainEvenOdd S T v ↔ ¬Layered.Ghost (pairCuts w) S T (pairVertexEquiv w v) := by
  rcases v with (⟨j,x⟩ | ⟨r,x⟩)
  · exact (pairVertex_even_retained w S T j x).symm
  · exact iff_of_true True.intro (pairVertex_odd_retained w S T r x)

/-- The coordinate transformation respects exactly the deleted boundary vertices. -/
noncomputable def retainedPairVertexEquiv {p : ℕ} (w : List (CutPair p)) (S T : State (2*p) p) :
    RetainedEven p w.length S T ⊕ OddVertex (2*p) w.length ≃ Layered.Retained (pairCuts w) S T :=
  (retainedSumEquiv S T).trans
    ((pairVertexEquiv w).subtypeEquiv (pairVertex_retained_iff w S T))

def retainedOriginalEmbedding {p h : ℕ} (S T : State (2*p) p) :
    (RetainedEven p h S T ⊕ OddVertex (2*p) h) ↪ (EvenVertex (2*p) h ⊕ OddVertex (2*p) h) :=
  (⟨Subtype.val,Subtype.val_injective⟩ : RetainedEven p h S T ↪ EvenVertex (2*p) h).sumMap
    (Function.Embedding.refl _)

 theorem retainedPairVertex_apply {p : ℕ} (w : List (CutPair p)) (S T : State (2*p) p)
    (v : RetainedEven p w.length S T ⊕ OddVertex (2*p) w.length) :
    (retainedPairVertexEquiv w S T v).val = pairVertexEquiv w (retainedOriginalEmbedding S T v) := by
  cases v <;> rfl

/-- The actual target cutGraph used in probe cancellation is isomorphic to the
actual boundary-retained PairEval graph, with no counting identity assumed. -/
noncomputable def monotoneTargetGraphIso {p : ℕ} (w : List (CutPair p)) (S T : State (2*p) p) :
    cutGraph (retainedTargetRelation (fun r => w.get r) S T) ≃g Layered.retainedGraph (pairCuts w) S T where
  toEquiv := retainedPairVertexEquiv w S T
  map_rel_iff' := by
    intro v u
    change (Layered.graph (pairCuts w)).Adj (retainedPairVertexEquiv w S T v).val
      (retainedPairVertexEquiv w S T u).val ↔ _
    rw [retainedPairVertex_apply,retainedPairVertex_apply,pairVertex_adjacency]
    cases v <;> cases u <;> rfl

/-- The exact target count required to finish the Section 9 numerical recovery. -/
theorem retainedTarget_matchingCount {p : ℕ} (w : List (CutPair p)) (S T : State (2*p) p) :
    (perfectMatchingCount (cutGraph (retainedTargetRelation (fun r => w.get r) S T)) : ℚ) =
      pairWordMatrix w S T := by
  rw [perfectMatchingCount_congr (monotoneTargetGraphIso w S T)]
  change (Layered.matchingCount (pairCuts w) S T : ℚ) = _
  rw [Layered.matchingCount_eq_transferProduct,pairCuts_transfer]

end HiddenCircuits.GraphReduction
