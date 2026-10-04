import HiddenCircuits.DH.LexBFSCellOrder

/-! Exact local contracts of the sparse neighbor-move loop. -/
namespace HiddenCircuits.DH.LexBFSPartition
open LexBFSLinks

@[simp] lemma removeVertex_owner_self {n b : ℕ} (s : Heap n b) (c : Fin b) (v : Fin n) :
    (removeVertex s c v).value.owner[v.val] = none := by
  rw [removeVertex_value]
  split_ifs <;> simp [removeCell,detached]

@[simp] lemma removeVertex_stamp {n b : ℕ} (s : Heap n b) (c : Fin b) (v : Fin n) :
    (removeVertex s c v).value.stamp = s.stamp := by
  rw [removeVertex_value]
  split_ifs <;> rfl

@[simp] lemma removeVertex_companion {n b : ℕ} (s : Heap n b) (c : Fin b) (v : Fin n) :
    (removeVertex s c v).value.companion = s.companion := by
  rw [removeVertex_value]
  split_ifs <;> rfl

@[simp] lemma appendVertex_stamp {n b : ℕ} (s : Heap n b) (c : Fin b) (v : Fin n) :
    (appendVertex s c v).value.stamp = s.stamp := rfl

@[simp] lemma appendVertex_companion {n b : ℕ} (s : Heap n b) (c : Fin b) (v : Fin n) :
    (appendVertex s c v).value.companion = s.companion := rfl

lemma moveNeighbor_absent {n b : ℕ} (s : Heap n b) (epoch : ℕ) (first : Bool) (v : Fin n)
    (hv : s.owner[v.val] = none) : (moveNeighbor s epoch first v).value = s := by
  simp [moveNeighbor,hv]

lemma moveNeighbor_existing {n b : ℕ} (s : Heap n b) (epoch : ℕ) (first : Bool) (v : Fin n)
    (c d : Fin b) (hv : s.owner[v.val] = some c) (hs : s.stamp[c.val] = epoch)
    (hd : s.companion[c.val] = some d) :
    (moveNeighbor s epoch first v).value =
      (appendVertex (removeVertex s c v).value d v).value := by
  simp [moveNeighbor,hv,hs,hd]

lemma moveNeighbor_new {n b : ℕ} (s : Heap n b) (epoch : ℕ) (first : Bool) (v : Fin n)
    (c : Fin b) (hv : s.owner[v.val] = some c) (hs : s.stamp[c.val] ≠ epoch)
    (hf : s.fresh < b) :
    (moveNeighbor s epoch first v).value =
      (appendVertex (removeVertex (newCompanion s c epoch first).value.2 c v).value
        ⟨s.fresh,hf⟩ v).value := by
  simp [moveNeighbor,hv,hs,newCompanion,hf]

/-- Moving into an existing companion erases and appends in exactly the two named cells. -/
theorem moveNeighbor_existing_view {n b : ℕ} {s : Heap n b} {f : CellContents n b}
    (h : VertexView s f) (epoch : ℕ) (first : Bool) (v : Fin n) (c d : Fin b)
    (hcd : c ≠ d) (pre post : List (Fin n)) (hc : f c = pre++v::post)
    (hs : s.stamp[c.val] = epoch) (hd : s.companion[c.val] = some d) :
    VertexView (moveNeighbor s epoch first v).value
      (Function.update (Function.update f c (pre++post)) d (f d++[v])) := by
  have hv : s.owner[v.val] = some c := (h.owner v c).mpr (by simp [hc])
  rw [moveNeighbor_existing s epoch first v c d hv hs hd]
  have hr := removeVertex_view h c v pre post hc
  have ha := appendVertex_view hr d v (removeVertex_owner_self s c v)
  simpa [Function.update,Ne.symm hcd] using ha

/-- A new companion gets a singleton; its predecessor cell retains exactly the other vertices. -/
theorem moveNeighbor_new_view {n b : ℕ} {s : Heap n b} {f : CellContents n b}
    (h : VertexView s f) (epoch : ℕ) (first : Bool) (v : Fin n) (c : Fin b)
    (pre post : List (Fin n)) (hc : f c = pre++v::post)
    (hs : s.stamp[c.val] ≠ epoch) (hf : s.fresh < b)
    (hcd : c ≠ (⟨s.fresh,hf⟩ : Fin b)) (hempty : f ⟨s.fresh,hf⟩ = []) :
    VertexView (moveNeighbor s epoch first v).value
      (Function.update (Function.update f c (pre++post)) ⟨s.fresh,hf⟩ [v]) := by
  have hv : s.owner[v.val] = some c := (h.owner v c).mpr (by simp [hc])
  rw [moveNeighbor_new s epoch first v c hv hs hf]
  have hn := newCompanion_view h c epoch first hf hempty
  have hr := removeVertex_view hn c v pre post hc
  have ha := appendVertex_view hr ⟨s.fresh,hf⟩ v (removeVertex_owner_self _ c v)
  simpa [Function.update,Ne.symm hcd,hempty] using ha

/-- Existing companions do not cross any cell; the only order change is removal of
an exhausted original cell. -/
theorem moveNeighbor_existing_order {n b : ℕ} {s : Heap n b}
    (epoch : ℕ) (first : Bool) (v : Fin n) (c d : Fin b)
    (pre post : List (Fin b)) (h : CellView s (pre++c::post))
    (hv : s.owner[v.val] = some c) (hs : s.stamp[c.val] = epoch)
    (hd : s.companion[c.val] = some d) :
    CellView (moveNeighbor s epoch first v).value
      (if s.size[c.val] = 1 then pre++post else pre++c::post) := by
  rw [moveNeighbor_existing s epoch first v c d hv hs hd]
  exact (removeVertex_order pre post c v h).appendVertex d v

/-- A newly allocated companion occupies exactly the stable split location, and an
exhausted old cell is removed without traversing any intervening cell. -/
theorem moveNeighbor_new_order {n b : ℕ} {s : Heap n b}
    (epoch : ℕ) (first : Bool) (v : Fin n) (c : Fin b)
    (pre post : List (Fin b)) (h : CellView s (pre++c::post))
    (hv : s.owner[v.val] = some c) (hs : s.stamp[c.val] ≠ epoch) (hf : s.fresh < b)
    (hnew : (⟨s.fresh,hf⟩ : Fin b) ∉ pre++c::post) :
    CellView (moveNeighbor s epoch first v).value
      (if s.size[c.val] = 1 then pre++⟨s.fresh,hf⟩::post else
        if first then pre++⟨s.fresh,hf⟩::c::post else pre++c::⟨s.fresh,hf⟩::post) := by
  let d : Fin b := ⟨s.fresh,hf⟩
  have hdc : d.val ≠ c.val := by
    intro he
    have hd : d = c := Fin.ext he
    exact hnew (by simp [← hd,d])
  have hz : (newCompanion s c epoch first).value.2.size[c.val] = s.size[c.val] := by
    simp [newCompanion,hf,← show d.val = s.fresh from rfl,hdc]
  rw [moveNeighbor_new s epoch first v c hv hs hf]
  have hi := newCompanion_order pre post c epoch first hf h hnew
  cases first
  · have hr := removeVertex_order pre (d::post) c v hi
    simpa [hz,d] using hr.appendVertex d v
  · have hi' : CellView (newCompanion s c epoch true).value.2 ((pre++[d])++c::post) := by
      simpa [List.append_assoc,d] using hi
    have hr := removeVertex_order (pre++[d]) post c v hi'
    simpa [hz,List.append_assoc,d] using hr.appendVertex d v

end HiddenCircuits.DH.LexBFSPartition
