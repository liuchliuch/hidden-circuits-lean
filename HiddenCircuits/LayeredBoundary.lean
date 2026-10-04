import HiddenCircuits.LayeredGraph
import HiddenCircuits.InducedPerfectMatching

namespace HiddenCircuits.Layered

/-- Partial inverse of the actual first-layer inclusion. -/
def firstDecode (p : ℕ) : (l : ℕ) → Vertices p l → Option (Fin (2*p))
  | 0, x => some x
  | _+1, .inl x => some x
  | _+1, .inr _ => none

@[simp] theorem firstDecode_some (p l : ℕ) (v : Vertices p l) (x : Fin (2*p)) :
    firstDecode p l v = some x ↔ v = first p l x := by
  cases l with
  | zero => simp only [firstDecode,first,Option.some.injEq]
  | succ l =>
    cases v with
    | inl y =>
      change (some y : Option (Fin (2*p))) = some x ↔
        (Sum.inl y : Fin (2*p) ⊕ Vertices p l) = Sum.inl x
      exact ⟨fun h => congrArg Sum.inl (Option.some.inj h),
        fun h => congrArg some (Sum.inl.inj h)⟩
    | inr v =>
      change (none : Option (Fin (2*p))) = some x ↔
        (Sum.inr v : Fin (2*p) ⊕ Vertices p l) = Sum.inl x
      simp

@[simp] theorem firstDecode_first (p l : ℕ) (x : Fin (2*p)) :
    firstDecode p l (first p l x) = some x := by
  rw [firstDecode_some]

 theorem first_eq_last {p l : ℕ} (x y : Fin (2*p)) (h : first p l x = last p l y) :
    l=0 ∧ x=y := by
  have hh := congrArg (layer p l) h
  simp only [layer_first,layer_last] at hh
  have hl : l=0 := hh.symm
  subst l
  exact ⟨rfl,h⟩

@[simp] theorem ghost_cons_left {p : ℕ} (R : UnweightedCut p) (w : List (UnweightedCut p))
    (S T : State (2*p) p) (x : Fin (2*p)) :
    Ghost (R::w) S T (.inl x) ↔ x ∉ S.val := by
  constructor
  · rintro (⟨y,hy,hyn⟩ | ⟨y,hy,_⟩)
    · have he : y=x := Sum.inl.inj hy
      exact he ▸ hyn
    · exact (Sum.inr_ne_inl hy).elim
  · intro hn
    exact Or.inl ⟨x,rfl,hn⟩

@[simp] theorem ghost_cons_right {p : ℕ} (R : UnweightedCut p) (w : List (UnweightedCut p))
    (S T : State (2*p) p) (v : Vertices p w.length) :
    Ghost (R::w) S T (.inr v) ↔ ∃ x, last p w.length x=v ∧ x ∈ T.val := by
  constructor
  · rintro (⟨y,hy,_⟩ | ⟨y,hy,hyt⟩)
    · exact (Sum.inl_ne_inr hy).elim
    · exact ⟨y,Sum.inr.inj hy,hyt⟩
  · rintro ⟨y,hy,hyt⟩
    exact Or.inr ⟨y,congrArg Sum.inr hy,hyt⟩

@[simp] theorem ghost_nil {p : ℕ} (S T : State (2*p) p) (x : Fin (2*p)) :
    Ghost [] S T x ↔ x ∉ S.val ∨ x ∈ T.val := by
  simp [Ghost,first,last]

/-- Boundary deletion changes no matching choices; it only removes the vertices
which the equivalent full-layer partner representation leaves unmatched. -/
noncomputable def boundaryPerfectEquiv {p : ℕ} (w : List (UnweightedCut p)) (S T : State (2*p) p) :
    BoundaryMatching w S T ≃ PerfectMatching (retainedGraph w S T) := by
  let e : BoundaryMatching w S T ≃ ExactMatching (graph w) {v | ¬ Ghost w S T v} :=
    (Equiv.refl (EncodedMatching (graph w))).subtypeEquiv (by
      intro m
      simp only [BoundaryCondition,Set.mem_setOf_eq,not_not]
      rfl)
  exact e.trans (exactMatchingPerfectEquiv (graph w) {v | ¬ Ghost w S T v})

 theorem matchingCount_eq_boundary {p : ℕ} (w : List (UnweightedCut p)) (S T : State (2*p) p) :
    matchingCount w S T = Fintype.card (BoundaryMatching w S T) :=
  Fintype.card_congr (boundaryPerfectEquiv w S T).symm

/-- The empty edge set is an actual graph matching. -/
def emptyMatching {V : Type*} (G : SimpleGraph V) : EncodedMatching G :=
  ⟨fun _ => none,by simp,by simp⟩

 theorem matching_bot_none {V : Type*} (m : EncodedMatching (⊥ : SimpleGraph V)) (v : V) :
    m.val v = none := by
  cases h : m.val v with
  | none => rfl
  | some w => exact (m.property.2 v w h).elim

/-- At zero cuts, the exact boundary condition forces equality of the endpoint states. -/
theorem boundary_nil_states {p : ℕ} (S T : State (2*p) p)
    (m : BoundaryMatching [] S T) : S=T := by
  apply Subtype.ext
  have hsub : S.val ⊆ T.val := by
    intro x hx
    have hh := (m.property x).mp (matching_bot_none m.val x)
    rcases (ghost_nil S T x).mp hh with hn | ht
    · exact (hn hx).elim
    · exact ht
  exact Finset.eq_of_subset_of_card_le hsub (by rw [S.property,T.property])

noncomputable def boundaryNilEquiv {p : ℕ} (S T : State (2*p) p) :
    BoundaryMatching [] S T ≃ PLift (S=T) where
  toFun m := ⟨boundary_nil_states S T m⟩
  invFun h := by
    rcases h with ⟨h⟩
    subst T
    refine ⟨emptyMatching _,?_⟩
    intro v
    simp only [emptyMatching,ghost_nil]
    tauto
  left_inv m := by
    apply Subtype.ext
    apply Subtype.ext
    funext v
    exact (matching_bot_none _ v).trans (matching_bot_none m.val v).symm
  right_inv h := Subsingleton.elim _ _

 theorem boundary_nil_card {p : ℕ} (S T : State (2*p) p) :
    Fintype.card (BoundaryMatching [] S T) = if S=T then 1 else 0 := by
  classical
  rw [Fintype.card_congr (boundaryNilEquiv S T)]
  by_cases h : S=T <;> simp [h]

end HiddenCircuits.Layered
