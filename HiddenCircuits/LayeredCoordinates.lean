import HiddenCircuits.LayeredMatching

/-! Actual layer/track coordinates of the recursive graph, with exact adjacency semantics. -/
namespace HiddenCircuits.Layered

theorem layer_lt (p l : ℕ) (v : Vertices p l) : layer p l v < l+1 := by
  induction l with
  | zero => simp [layer]
  | succ l ih =>
    cases v with
    | inl x => simp [layer]
    | inr v => have h := ih v; change layer p l v+1 < l+1+1; omega

@[simp] theorem track_first (p l : ℕ) (x : Fin (2*p)) : track p l (first p l x)=x := by
  cases l <;> rfl
@[simp] theorem track_last (p l : ℕ) (x : Fin (2*p)) : track p l (last p l x)=x := by
  induction l with
  | zero => rfl
  | succ l ih => exact ih

/-- Construct the unique actual vertex at a stated layer and track. -/
def vertexAt (p : ℕ) : (l : ℕ) → Fin (l+1) → Fin (2*p) → Vertices p l
  | 0,_,x => x
  | l+1,i,x => Fin.cases (.inl x) (fun j => .inr (vertexAt p l j x)) i

@[simp] theorem vertexAt_layer (p l : ℕ) (i : Fin (l+1)) (x : Fin (2*p)) :
    layer p l (vertexAt p l i x)=i.val := by
  induction l with
  | zero => have hi := i.isLt; change 0=i.val; omega
  | succ l ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change layer p l (vertexAt p l j x)+1=j.val+1
      rw [ih]

@[simp] theorem vertexAt_track (p l : ℕ) (i : Fin (l+1)) (x : Fin (2*p)) :
    track p l (vertexAt p l i x)=x := by
  induction l with
  | zero => rfl
  | succ l ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact ih j

 theorem vertexAt_coordinates (p l : ℕ) (v : Vertices p l) :
    vertexAt p l ⟨layer p l v,layer_lt p l v⟩ (track p l v)=v := by
  induction l with
  | zero => rfl
  | succ l ih =>
    cases v with
    | inl x => rfl
    | inr v =>
      change Sum.inr (vertexAt p l ⟨layer p l v,layer_lt p l v⟩ (track p l v)) = Sum.inr v
      rw [ih]

/-- The recursive vertices are exactly the labeled layer/track grid. -/
def coordinateEquiv (p l : ℕ) : Vertices p l ≃ Fin (l+1) × Fin (2*p) where
  toFun v := (⟨layer p l v,layer_lt p l v⟩,track p l v)
  invFun v := vertexAt p l v.1 v.2
  left_inv := vertexAt_coordinates p l
  right_inv v := Prod.ext (Fin.ext (vertexAt_layer p l v.1 v.2)) (vertexAt_track p l v.1 v.2)

 theorem vertex_ext {p l : ℕ} (v u : Vertices p l)
    (hl : layer p l v=layer p l u) (ht : track p l v=track p l u) : v=u :=
  (coordinateEquiv p l).injective (Prod.ext (Fin.ext hl) ht)

 theorem first_of_layer_zero {p l : ℕ} (v : Vertices p l) (h : layer p l v=0) :
    first p l (track p l v)=v := by
  apply vertex_ext
  · simpa only [layer_first] using h.symm
  · exact track_first p l _
 theorem last_of_layer_last {p l : ℕ} (v : Vertices p l) (h : layer p l v=l) :
    last p l (track p l v)=v := by
  apply vertex_ext
  · simpa only [layer_last] using h.symm
  · exact track_last p l _

/-- Boundary deletion expressed entirely through the actual layer and track labels. -/
theorem ghost_coordinates {p : ℕ} (w : List (UnweightedCut p)) (S T : State (2*p) p)
    (v : Vertices p w.length) :
    Ghost w S T v ↔ (layer p w.length v=0 ∧ track p w.length v ∉ S.val) ∨
      (layer p w.length v=w.length ∧ track p w.length v ∈ T.val) := by
  constructor
  · rintro (⟨x,rfl,hx⟩ | ⟨x,rfl,hx⟩)
    · exact Or.inl ⟨layer_first p w.length x,by simpa only [track_first] using hx⟩
    · exact Or.inr ⟨layer_last p w.length x,by simpa only [track_last] using hx⟩
  · rintro (⟨hl,hx⟩ | ⟨hl,hx⟩)
    · exact Or.inl ⟨track p w.length v,first_of_layer_zero v hl,hx⟩
    · exact Or.inr ⟨track p w.length v,last_of_layer_last v hl,hx⟩

/-- Out-of-range cuts contain no edges; within range this is the literal listed cut. -/
def cutAt {p : ℕ} : List (UnweightedCut p) → ℕ → UnweightedCut p
  | [],_ => fun _ _ => false
  | R::_,0 => R
  | _::w,i+1 => cutAt w i

/-- Exact edge characterization: consecutive layers and the corresponding supplied Boolean cut. -/
theorem graph_adj_coordinates {p : ℕ} (w : List (UnweightedCut p))
    (v u : Vertices p w.length) :
    (graph w).Adj v u ↔
      (layer p w.length v+1=layer p w.length u ∧
        cutAt w (layer p w.length v) (track p w.length v) (track p w.length u)=true) ∨
      (layer p w.length u+1=layer p w.length v ∧
        cutAt w (layer p w.length u) (track p w.length u) (track p w.length v)=true) := by
  induction w with
  | nil => change False ↔ (1=0 ∧ false=true) ∨ (1=0 ∧ false=true); simp
  | cons R w ih =>
    cases v with
    | inl x =>
      cases u with
      | inl y => change False ↔ (1=0 ∧ R x y=true) ∨ (1=0 ∧ R y x=true); simp
      | inr u =>
        change (∃ y, first p w.length y=u ∧ R x y=true) ↔
          (1=layer p w.length u+1 ∧ R x (track p w.length u)=true) ∨
          (layer p w.length u+1+1=0 ∧ cutAt w (layer p w.length u) (track p w.length u) x=true)
        constructor
        · rintro ⟨y,rfl,hr⟩
          exact Or.inl ⟨by simp,by simpa only [track_first] using hr⟩
        · rintro (⟨hl,hr⟩ | ⟨hl,_⟩)
          · exact ⟨track p w.length u,first_of_layer_zero u (by omega),hr⟩
          · omega
    | inr v =>
      cases u with
      | inl x =>
        change (∃ y, first p w.length y=v ∧ R x y=true) ↔
          (layer p w.length v+1+1=0 ∧ cutAt w (layer p w.length v) (track p w.length v) x=true) ∨
          (1=layer p w.length v+1 ∧ R x (track p w.length v)=true)
        constructor
        · rintro ⟨y,rfl,hr⟩
          exact Or.inr ⟨by simp,by simpa only [track_first] using hr⟩
        · rintro (⟨hl,_⟩ | ⟨hl,hr⟩)
          · omega
          · exact ⟨track p w.length v,first_of_layer_zero v (by omega),hr⟩
      | inr u =>
        change (graph w).Adj v u ↔
          ((layer p w.length v+1)+1=layer p w.length u+1 ∧
            cutAt w (layer p w.length v) (track p w.length v) (track p w.length u)=true) ∨
          ((layer p w.length u+1)+1=layer p w.length v+1 ∧
            cutAt w (layer p w.length u) (track p w.length u) (track p w.length v)=true)
        simpa only [Nat.add_right_cancel_iff] using ih v u

/-- Relabel an equal-length recursive layer space without changing any coordinate. -/
def castVertices {p l m : ℕ} (h : l=m) (v : Vertices p l) : Vertices p m := h ▸ v
@[simp] theorem layer_castVertices {p l m : ℕ} (h : l=m) (v : Vertices p l) :
    layer p m (castVertices h v)=layer p l v := by subst m; rfl
@[simp] theorem track_castVertices {p l m : ℕ} (h : l=m) (v : Vertices p l) :
    track p m (castVertices h v)=track p l v := by subst m; rfl

end HiddenCircuits.Layered
