import HiddenCircuits.LayeredCoordinates
import HiddenCircuits.GraphReduction.MonotoneVertices

/-! Exact even/odd layer coordinates of the actual paired layered graph. -/
namespace HiddenCircuits.GraphReduction

/-- The actual interleaving of even and odd layer labels. -/
def evenOddLayer (h : ℕ) : Fin (h+1) ⊕ Fin h → Fin (2*h+1)
  | .inl j => ⟨2*j.val,by have := j.isLt; omega⟩
  | .inr r => ⟨2*r.val+1,by have := r.isLt; omega⟩

 theorem evenOddLayer_injective (h : ℕ) : Function.Injective (evenOddLayer h) := by
  intro x y he
  have hv := congrArg Fin.val he
  cases x with
  | inl j =>
    cases y with
    | inl k => exact congrArg Sum.inl (Fin.ext (by change 2*j.val=2*k.val at hv; omega))
    | inr r => change 2*j.val=2*r.val+1 at hv; omega
  | inr r =>
    cases y with
    | inl j => change 2*r.val+1=2*j.val at hv; omega
    | inr t => exact congrArg Sum.inr (Fin.ext (by change 2*r.val+1=2*t.val+1 at hv; omega))

 theorem evenOddLayer_surjective (h : ℕ) : Function.Surjective (evenOddLayer h) := by
  intro i
  have hi := i.isLt
  by_cases he : i.val%2=0
  · refine ⟨.inl ⟨i.val/2,by omega⟩,?_⟩
    apply Fin.ext
    change 2*(i.val/2)=i.val
    omega
  · refine ⟨.inr ⟨i.val/2,by omega⟩,?_⟩
    apply Fin.ext
    change 2*(i.val/2)+1=i.val
    omega

noncomputable def evenOddLayerEquiv (h : ℕ) : Fin (h+1) ⊕ Fin h ≃ Fin (2*h+1) :=
  Equiv.ofBijective (evenOddLayer h) ⟨evenOddLayer_injective h,evenOddLayer_surjective h⟩

/-- Group a common track coordinate independently of the layer-color choice. -/
def groupTrackEquiv (A B C : Type*) : (A × C) ⊕ (B × C) ≃ (A ⊕ B) × C where
  toFun
    | .inl (a,c) => (.inl a,c)
    | .inr (b,c) => (.inr b,c)
  invFun
    | (.inl a,c) => .inl (a,c)
    | (.inr b,c) => .inr (b,c)
  left_inv := by intro x; cases x <;> rfl
  right_inv := by rintro ⟨a | b,c⟩ <;> rfl

noncomputable def parityCoordinateEquiv (n h : ℕ) :
    EvenVertex n h ⊕ OddVertex n h ≃ Fin (2*h+1) × Fin n :=
  (groupTrackEquiv _ _ _).trans ((evenOddLayerEquiv h).prodCongr (Equiv.refl _))

/-- Equality transport of a recursive layer space, as an actual equivalence. -/
def vertexLengthEquiv {p l m : ℕ} (h : l=m) : Layered.Vertices p l ≃ Layered.Vertices p m :=
  Equiv.cast (congrArg (Layered.Vertices p) h)

@[simp] theorem layer_vertexLengthEquiv {p l m : ℕ} (h : l=m) (v : Layered.Vertices p l) :
    Layered.layer p m (vertexLengthEquiv h v)=Layered.layer p l v := by subst m; rfl
@[simp] theorem track_vertexLengthEquiv {p l m : ℕ} (h : l=m) (v : Layered.Vertices p l) :
    Layered.track p m (vertexLengthEquiv h v)=Layered.track p l v := by subst m; rfl

/-- The even/odd labels are exactly the actual recursively grouped pair-cut vertices. -/
noncomputable def pairVertexEquiv {p : ℕ} (w : List (CutPair p)) :
    EvenVertex (2*p) w.length ⊕ OddVertex (2*p) w.length ≃
      Layered.Vertices p (pairCuts w).length :=
  (parityCoordinateEquiv (2*p) w.length).trans
    ((Layered.coordinateEquiv p (2*w.length)).symm.trans
      (vertexLengthEquiv (pairCuts_length w).symm))

 theorem pairVertex_layer {p : ℕ} (w : List (CutPair p))
    (v : EvenVertex (2*p) w.length ⊕ OddVertex (2*p) w.length) :
    Layered.layer p (pairCuts w).length (pairVertexEquiv w v) =
      (parityCoordinateEquiv (2*p) w.length v).1.val := by
  change Layered.layer p (pairCuts w).length
    (vertexLengthEquiv (pairCuts_length w).symm
      (Layered.vertexAt p (2*w.length) (parityCoordinateEquiv (2*p) w.length v).1
        (parityCoordinateEquiv (2*p) w.length v).2)) = _
  rw [layer_vertexLengthEquiv,Layered.vertexAt_layer]

 theorem pairVertex_track {p : ℕ} (w : List (CutPair p))
    (v : EvenVertex (2*p) w.length ⊕ OddVertex (2*p) w.length) :
    Layered.track p (pairCuts w).length (pairVertexEquiv w v) =
      (parityCoordinateEquiv (2*p) w.length v).2 := by
  change Layered.track p (pairCuts w).length
    (vertexLengthEquiv (pairCuts_length w).symm
      (Layered.vertexAt p (2*w.length) (parityCoordinateEquiv (2*p) w.length v).1
        (parityCoordinateEquiv (2*p) w.length v).2)) = _
  rw [track_vertexLengthEquiv,Layered.vertexAt_track]

@[simp] theorem pairVertex_even_layer {p : ℕ} (w : List (CutPair p))
    (j : Fin (w.length+1)) (x : Fin (2*p)) :
    Layered.layer p (pairCuts w).length (pairVertexEquiv w (.inl (j,x)))=2*j.val :=
  pairVertex_layer w _
@[simp] theorem pairVertex_odd_layer {p : ℕ} (w : List (CutPair p))
    (r : Fin w.length) (x : Fin (2*p)) :
    Layered.layer p (pairCuts w).length (pairVertexEquiv w (.inr (r,x)))=2*r.val+1 :=
  pairVertex_layer w _
@[simp] theorem pairVertex_even_track {p : ℕ} (w : List (CutPair p))
    (j : Fin (w.length+1)) (x : Fin (2*p)) :
    Layered.track p (pairCuts w).length (pairVertexEquiv w (.inl (j,x)))=x :=
  pairVertex_track w _
@[simp] theorem pairVertex_odd_track {p : ℕ} (w : List (CutPair p))
    (r : Fin w.length) (x : Fin (2*p)) :
    Layered.track p (pairCuts w).length (pairVertexEquiv w (.inr (r,x)))=x :=
  pairVertex_track w _

/-- Exact indexing of both cut matrices of every listed pair. -/
theorem cutAt_pair_even {p : ℕ} (w : List (CutPair p)) (r : Fin w.length) :
    Layered.cutAt (pairCuts w) (2*r.val) = (w.get r).firstCut := by
  induction w with
  | nil => exact Fin.elim0 r
  | cons P w ih =>
    refine Fin.cases ?_ (fun r => ?_) r
    · rfl
    · change Layered.cutAt (pairCuts w) (2*r.val) = (w.get r).firstCut
      exact ih r

 theorem cutAt_pair_odd {p : ℕ} (w : List (CutPair p)) (r : Fin w.length) :
    Layered.cutAt (pairCuts w) (2*r.val+1) = (w.get r).secondCut := by
  induction w with
  | nil => exact Fin.elim0 r
  | cons P w ih =>
    refine Fin.cases ?_ (fun r => ?_) r
    · rfl
    · change Layered.cutAt (pairCuts w) (2*r.val+1) = (w.get r).secondCut
      exact ih r

/-- The first and second actual cuts agree exactly with the target even/odd relation. -/
theorem pairVertex_even_odd_adj {p : ℕ} (w : List (CutPair p))
    (j : Fin (w.length+1)) (r : Fin w.length) (x y : Fin (2*p)) :
    (Layered.graph (pairCuts w)).Adj (pairVertexEquiv w (.inl (j,x))) (pairVertexEquiv w (.inr (r,y))) ↔
      targetRelation (fun r => w.get r) (j,x) (r,y) := by
  rw [Layered.graph_adj_coordinates]
  simp only [pairVertex_even_layer,pairVertex_odd_layer,pairVertex_even_track,pairVertex_odd_track,targetRelation]
  have he : 2*j.val+1=2*r.val+1 ↔ j.val=r.val := by omega
  have ho : (2*r.val+1)+1=2*j.val ↔ j.val=r.val+1 := by omega
  rw [he,ho]
  apply or_congr
  · apply and_congr_right
    intro hj
    rw [hj,cutAt_pair_even]
    simp only [CutPair.firstCut,decide_eq_true_eq]
  · apply and_congr_right
    intro _
    rw [cutAt_pair_odd]
    simp only [CutPair.secondCut,decide_eq_true_eq]

 theorem pairVertex_adjacency {p : ℕ} (w : List (CutPair p))
    (v u : EvenVertex (2*p) w.length ⊕ OddVertex (2*p) w.length) :
    (Layered.graph (pairCuts w)).Adj (pairVertexEquiv w v) (pairVertexEquiv w u) ↔
      (cutGraph (targetRelation (fun r => w.get r))).Adj v u := by
  rcases v with (⟨j,x⟩ | ⟨r,x⟩) <;> rcases u with (⟨k,y⟩ | ⟨t,y⟩)
  · constructor
    · intro hh
      have hc := Layered.graph_adj_consecutive (pairCuts w) _ _ hh
      simp only [pairVertex_even_layer] at hc
      omega
    · intro hh
      exact hh.elim
  · exact pairVertex_even_odd_adj w j t x y
  · exact ⟨fun h => (pairVertex_even_odd_adj w k r y x).mp h.symm,
      fun h => ((pairVertex_even_odd_adj w k r y x).mpr h).symm⟩
  · constructor
    · intro hh
      have hc := Layered.graph_adj_consecutive (pairCuts w) _ _ hh
      simp only [pairVertex_odd_layer] at hc
      omega
    · intro hh
      exact hh.elim

/-- An actual graph isomorphism before the boundary vertices are deleted. -/
noncomputable def pairedFullGraphIso {p : ℕ} (w : List (CutPair p)) :
    cutGraph (targetRelation (fun r => w.get r)) ≃g Layered.graph (pairCuts w) where
  toEquiv := pairVertexEquiv w
  map_rel_iff' := pairVertex_adjacency w _ _

end HiddenCircuits.GraphReduction
