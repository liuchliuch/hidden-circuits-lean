import HiddenCircuits.DH.LexBFSPartition

/-! Ghost refinement relations for the direct-pointer partition heap. Neither cell
lists nor ordered partitions occur in the executable heap. -/
namespace HiddenCircuits.DH.LexBFSPartition
open LexBFSLinks

abbrev CellContents (n b : ℕ) := Fin b → List (Fin n)

/-- Exact interpretation of every vertex array and the stored cell endpoints/sizes. -/
structure VertexView {n b : ℕ} (s : Heap n b) (f : CellContents n b) : Prop where
  nodup : ∀ c, (f c).Nodup
  links : ∀ c, Realizes s.vertices (f c)
  owner : ∀ v c, s.owner[v.val] = some c ↔ v ∈ f c
  head : ∀ c, s.head[c.val] = (f c).head?
  tail : ∀ c, s.tail[c.val] = (f c).getLast?
  size : ∀ c, s.size[c.val] = (f c).length

lemma VertexView.disjoint {n b : ℕ} {s : Heap n b} {f : CellContents n b}
    (h : VertexView s f) {c d : Fin b} (hne : c ≠ d) : List.Disjoint (f c) (f d) := by
  apply List.disjoint_left.mpr
  intro v hc hd
  have he := (h.owner v c).mpr hc
  have he' := (h.owner v d).mpr hd
  exact hne (Option.some.inj (he.symm.trans he'))

lemma VertexView.absent {n b : ℕ} {s : Heap n b} {f : CellContents n b}
    (h : VertexView s f) {v : Fin n} (hv : s.owner[v.val] = none) (c : Fin b) : v ∉ f c := by
  intro hc
  have he := (h.owner v c).mpr hc
  simp [hv] at he

/-- A constant-time append implements a stable append in precisely one ghost cell. -/
theorem appendVertex_view {n b : ℕ} {s : Heap n b} {f : CellContents n b}
    (h : VertexView s f) (c : Fin b) (v : Fin n) (hv : s.owner[v.val] = none) :
    VertexView (appendVertex s c v).value (Function.update f c (f c++[v])) := by
  have hva := h.absent hv
  constructor
  · intro d
    by_cases hd : d = c
    · subst d
      simp only [Function.update_self]
      refine List.nodup_append.mpr ⟨h.nodup c,by simp,?_⟩
      intro a ha b hb he
      have hb' : b = v := List.mem_singleton.mp hb
      exact hva c ((he.trans hb') ▸ ha)
    · simpa [Function.update,hd] using h.nodup d
  · intro d
    by_cases hd : d = c
    · subst d
      simpa [appendVertex,h.tail c] using
        insert_realizes (a := s.vertices) (f c) [] v (by simpa using h.links c) (by simpa using h.nodup c) (by simpa using hva c)
    · have hl : ∀ x ∈ f d, s.tail[c.val] ≠ some x := by
        intro x hx he
        rw [h.tail c] at he
        exact (List.disjoint_left.mp (h.disjoint (Ne.symm hd)) (List.mem_of_getLast? he)) hx
      have hh := insert_frame v s.tail[c.val] none (h.links d) (hva d) hl (by simp)
      simpa [appendVertex,Function.update,hd] using hh
  · intro w d
    by_cases hw : w = v
    · subst w
      by_cases hd : d = c
      · subst d; simp [appendVertex]
      · simp [appendVertex,Function.update,hd,Ne.symm hd,hva d]
    · have hvw : v.val ≠ w.val := fun he => hw (Fin.ext he).symm
      by_cases hd : d = c
      · subst d
        simpa [appendVertex,hvw,hw] using h.owner w c
      · simpa [appendVertex,hvw,Function.update,hd] using h.owner w d
  · intro d
    by_cases hd : d = c
    · subst d
      dsimp only [appendVertex]
      rw [h.tail c]
      cases hc : f c with
      | nil => simp [hc]
      | cons a as =>
        have hn : (a::as).getLast? ≠ none := by simp
        simp [hc,hn,h.head c]
    · have hcd : c.val ≠ d.val := fun he => hd (Fin.ext he).symm
      simp only [appendVertex]
      split_ifs <;> simpa [Function.update,hd,hcd] using h.head d
  · intro d
    by_cases hd : d = c
    · subst d; simp [appendVertex]
    · have hcd : c.val ≠ d.val := fun he => hd (Fin.ext he).symm
      simpa [appendVertex,Function.update,hd,hcd] using h.tail d
  · intro d
    by_cases hd : d = c
    · subst d; simp [appendVertex,h.size c]
    · have hcd : c.val ≠ d.val := fun he => hd (Fin.ext he).symm
      simpa [appendVertex,Function.update,hd,hcd] using h.size d

/-- The vertex-array portion of removal, before possibly unlinking an empty cell. -/
def detached {n b : ℕ} (s : Heap n b) (c : Fin b) (v : Fin n) : Heap n b :=
  {s with
    vertices := unlink s.vertices v
    owner := s.owner.set v.val none
    head := if s.vertices.prev[v.val] = none then s.head.set c.val s.vertices.next[v.val] else s.head
    tail := if s.vertices.next[v.val] = none then s.tail.set c.val s.vertices.prev[v.val] else s.tail
    size := s.size.set c.val (s.size[c.val]-1)}

lemma removeVertex_value {n b : ℕ} (s : Heap n b) (c : Fin b) (v : Fin n) :
    (removeVertex s c v).value =
      if s.size[c.val] = 1 then (removeCell (detached s c v) c).value else detached s c v := by
  by_cases hs : s.size[c.val] = 1 <;> simp [removeVertex,detached,hs]

lemma removeCell_view {n b : ℕ} {s : Heap n b} {f : CellContents n b}
    (h : VertexView s f) (c : Fin b) : VertexView (removeCell s c).value f := by
  exact ⟨h.nodup,h.links,h.owner,h.head,h.tail,h.size⟩

lemma nodup_remove_middle {α : Type*} (pre post : List α) (v : α)
    (h : (pre++v::post).Nodup) : (pre++post).Nodup := by
  obtain ⟨hp,ht,hd⟩ := List.nodup_append.mp h
  exact List.nodup_append.mpr ⟨hp,(List.nodup_cons.mp ht).2,
    fun x hx y hy => hd x hx y (List.mem_cons_of_mem _ hy)⟩

/-- Direct removal changes precisely the known owner's ghost list. -/
theorem detached_view {n b : ℕ} {s : Heap n b} {f : CellContents n b}
    (h : VertexView s f) (c : Fin b) (v : Fin n) (pre post : List (Fin n))
    (hc : f c = pre++v::post) :
    VertexView (detached s c v) (Function.update f c (pre++post)) := by
  have hlinks : Realizes s.vertices (pre++v::post) := hc ▸ h.links c
  have hnd : (pre++v::post).Nodup := hc ▸ h.nodup c
  have hn := hlinks.1.at pre post v
  have hrev : Forward s.vertices.prev (post.reverse++v::pre.reverse) none := by
    simpa [List.reverse_append,List.reverse_cons,List.append_assoc] using hlinks.2
  have hp := hrev.at post.reverse pre.reverse v
  simp only [List.head?_reverse] at hp
  have hv : v ∈ f c := by simp [hc]
  have hvo := (h.owner v c).mpr hv
  have hvrest : v ∉ pre++post := by
    have hh := List.nodup_append.mp hnd
    intro hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hh.2.2 v hm v List.mem_cons_self rfl
    · exact (List.nodup_cons.mp hh.2.1).1 hm
  constructor
  · intro d
    by_cases hd : d = c
    · subst d; simpa using nodup_remove_middle pre post v hnd
    · simpa [Function.update,hd] using h.nodup d
  · intro d
    by_cases hd : d = c
    · subst d
      simpa [detached] using unlink_realizes pre post v hlinks hnd
    · have hp' : ∀ x ∈ f d, s.vertices.prev[v.val] ≠ some x := by
        intro x hx he
        rw [hp] at he
        have hxc : x ∈ f c := by simp only [hc,List.mem_append,List.mem_cons]; exact Or.inl (List.mem_of_getLast? he)
        exact (List.disjoint_left.mp (h.disjoint (Ne.symm hd)) hxc) hx
      have hn' : ∀ x ∈ f d, s.vertices.next[v.val] ≠ some x := by
        intro x hx he
        rw [hn] at he
        have hxc : x ∈ f c := by simp only [hc,List.mem_append,List.mem_cons]; exact Or.inr (Or.inr (List.mem_of_head? he))
        exact (List.disjoint_left.mp (h.disjoint (Ne.symm hd)) hxc) hx
      simpa [detached,Function.update,hd] using unlink_frame v (h.links d) hp' hn'
  · intro w d
    by_cases hw : w = v
    · subst w
      by_cases hd : d = c
      · subst d; simp [detached,hvrest]
      · have hvd : v ∉ f d := (List.disjoint_left.mp (h.disjoint (Ne.symm hd))) hv
        simp [detached,Function.update,hd,hvd]
    · have hvw : v.val ≠ w.val := fun he => hw (Fin.ext he).symm
      by_cases hd : d = c
      · subst d
        simpa [detached,hvw,hc,hw] using h.owner w c
      · simpa [detached,hvw,Function.update,hd] using h.owner w d
  · intro d
    by_cases hd : d = c
    · subst d
      dsimp only [detached]
      rw [hp,hn]
      cases pre with
      | nil => simp
      | cons x xs => simp [h.head c,hc]
    · have hcd : c.val ≠ d.val := fun he => hd (Fin.ext he).symm
      dsimp only [detached]
      split_ifs <;> simpa [Function.update,hd,hcd] using h.head d
  · intro d
    by_cases hd : d = c
    · subst d
      dsimp only [detached]
      rw [hp,hn]
      cases post with
      | nil => simp
      | cons x xs => simp [h.tail c,hc]
    · have hcd : c.val ≠ d.val := fun he => hd (Fin.ext he).symm
      dsimp only [detached]
      split_ifs <;> simpa [Function.update,hd,hcd] using h.tail d
  · intro d
    by_cases hd : d = c
    · subst d; simp [detached,h.size c,hc]
    · have hcd : c.val ≠ d.val := fun he => hd (Fin.ext he).symm
      simpa [detached,Function.update,hd,hcd] using h.size d

/-- The full removal primitive, including deletion of an empty cell, is exact on all
vertex pointers, memberships, stored endpoints and stored sizes. -/
theorem removeVertex_view {n b : ℕ} {s : Heap n b} {f : CellContents n b}
    (h : VertexView s f) (c : Fin b) (v : Fin n) (pre post : List (Fin n))
    (hc : f c = pre++v::post) :
    VertexView (removeVertex s c v).value (Function.update f c (pre++post)) := by
  rw [removeVertex_value]
  split_ifs
  · exact removeCell_view (detached_view h c v pre post hc) c
  · exact detached_view h c v pre post hc

end HiddenCircuits.DH.LexBFSPartition
