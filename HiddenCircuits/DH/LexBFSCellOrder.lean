import HiddenCircuits.DH.LexBFSView

/-! Exact refinement of the intrusive ordered cell list. -/
namespace HiddenCircuits.DH.LexBFSPartition
open LexBFSLinks

structure CellView {n b : ℕ} (s : Heap n b) (cs : List (Fin b)) : Prop where
  nodup : cs.Nodup
  links : Realizes s.cells cs
  first : s.first = cs.head?

lemma CellView.detached {n b : ℕ} {s : Heap n b} {cs : List (Fin b)}
    (h : CellView s cs) (c : Fin b) (v : Fin n) : CellView (detached s c v) cs :=
  ⟨h.nodup,h.links,h.first⟩

lemma CellView.appendVertex {n b : ℕ} {s : Heap n b} {cs : List (Fin b)}
    (h : CellView s cs) (c : Fin b) (v : Fin n) : CellView (appendVertex s c v).value cs :=
  ⟨h.nodup,h.links,h.first⟩

/-- Removing a cell changes exactly its two adjacent cell links and possibly the first-cell register. -/
theorem removeCell_order {n b : ℕ} {s : Heap n b} (pre post : List (Fin b)) (c : Fin b)
    (h : CellView s (pre++c::post)) : CellView (removeCell s c).value (pre++post) := by
  refine ⟨nodup_remove_middle pre post c h.nodup,
    unlink_realizes pre post c h.links h.nodup,?_⟩
  have hn := h.links.1.at pre post c
  dsimp only [removeCell]
  rw [hn,h.first]
  cases pre with
  | nil => simp
  | cons a as =>
    have hne : a ≠ c := by
      intro he
      subst a
      exact (List.nodup_cons.mp h.nodup).1 (by simp)
    simp [hne]

lemma removeVertex_order {n b : ℕ} {s : Heap n b} (pre post : List (Fin b)) (c : Fin b)
    (v : Fin n) (h : CellView s (pre++c::post)) :
    CellView (removeVertex s c v).value
      (if s.size[c.val] = 1 then pre++post else pre++c::post) := by
  rw [removeVertex_value]
  split_ifs
  · exact removeCell_order pre post c (h.detached c v)
  · exact h.detached c v

/-- Inserted companion IDs are literal fresh array indices, in the requested side of
precisely the source cell; pre-existing cells never cross each other. -/
theorem newCompanion_order {n b : ℕ} {s : Heap n b} (pre post : List (Fin b)) (c : Fin b)
    (epoch : ℕ) (first : Bool) (hf : s.fresh < b)
    (h : CellView s (pre++c::post))
    (hnew : (⟨s.fresh,hf⟩ : Fin b) ∉ pre++c::post) :
    CellView (newCompanion s c epoch first).value.2
      (if first then pre++⟨s.fresh,hf⟩::c::post else pre++c::⟨s.fresh,hf⟩::post) := by
  let d : Fin b := ⟨s.fresh,hf⟩
  have hn := h.links.1.at pre post c
  have hr : Forward s.cells.prev (post.reverse++c::pre.reverse) none := by
    simpa [List.reverse_append,List.reverse_cons,List.append_assoc] using h.links.2
  have hp := hr.at post.reverse pre.reverse c
  simp only [List.head?_reverse] at hp
  cases first
  · have hi := insert_realizes (a := s.cells) (pre++[c]) post d
      (by simpa [List.append_assoc] using h.links)
      (by simpa [List.append_assoc] using h.nodup)
      (by simpa [List.append_assoc,d] using hnew)
    constructor
    · have hd : (pre++c::d::post).Perm (d::(pre++c::post)) := by
        simpa [List.append_assoc] using (List.perm_middle : ((pre++[c])++d::post).Perm (d::((pre++[c])++post)))
      apply hd.nodup_iff.mpr
      exact List.nodup_cons.mpr ⟨hnew,h.nodup⟩
    · simpa [newCompanion,hf,hn,List.append_assoc,d] using hi
    · simp only [newCompanion,hf,↓reduceDIte,Bool.false_eq_true,↓reduceIte,
        Bool.false_and,Bool.false_eq_true]
      simpa using h.first
  · have hi := insert_realizes (a := s.cells) pre (c::post) d h.links h.nodup hnew
    constructor
    · have hd : (pre++d::c::post).Perm (d::(pre++c::post)) :=
        List.perm_middle
      exact hd.nodup_iff.mpr (List.nodup_cons.mpr ⟨hnew,h.nodup⟩)
    · simpa [newCompanion,hf,hp,d] using hi
    · dsimp only [newCompanion]
      simp only [hf,↓reduceDIte,↓reduceIte,Bool.true_and]
      rw [h.first]
      cases pre with
      | nil => simp
      | cons a as =>
        have hne : a ≠ c := by
          intro he
          subst a
          exact (List.nodup_cons.mp h.nodup).1 (by simp)
        simp [hne]

/-- Allocating an empty companion does not change any original-vertex list or owner. -/
theorem newCompanion_view {n b : ℕ} {s : Heap n b} {f : CellContents n b}
    (h : VertexView s f) (c : Fin b) (epoch : ℕ) (first : Bool) (hf : s.fresh < b)
    (hempty : f ⟨s.fresh,hf⟩ = []) : VertexView (newCompanion s c epoch first).value.2 f := by
  constructor
  · exact h.nodup
  · intro d; simpa [newCompanion,hf] using h.links d
  · intro v d; simpa [newCompanion,hf] using h.owner v d
  · intro d
    by_cases hd : d.val = s.fresh
    · have he : d = ⟨s.fresh,hf⟩ := Fin.ext hd
      subst d
      simp [newCompanion,hf,hempty]
    · simpa [newCompanion,hf,Ne.symm hd] using h.head d
  · intro d
    by_cases hd : d.val = s.fresh
    · have he : d = ⟨s.fresh,hf⟩ := Fin.ext hd
      subst d
      simp [newCompanion,hf,hempty]
    · simpa [newCompanion,hf,Ne.symm hd] using h.tail d
  · intro d
    by_cases hd : d.val = s.fresh
    · have he : d = ⟨s.fresh,hf⟩ := Fin.ext hd
      subst d
      simp [newCompanion,hf,hempty]
    · simpa [newCompanion,hf,Ne.symm hd] using h.size d

end HiddenCircuits.DH.LexBFSPartition
