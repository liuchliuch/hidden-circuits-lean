import HiddenCircuits.DH.LexBFSAdvance

/-! Simulation of one sparse neighbor transfer by the concrete pointer heap. -/
namespace HiddenCircuits.DH.LexBFSPartition
open LexBFSLinks
open LexBFSLabeled (Block)

lemma BlockView.separate {n b : ℕ} {s : Heap n b} {epoch : ℕ} {first : Bool}
    {bs : List (Block n b)} {f : CellContents n b} (h : BlockView s epoch first bs f) :
    LexBFSLabeled.Separate bs := by
  have hi := h.ids
  change (bs.flatMap blockIds).Pairwise (· ≠ ·) at hi
  have hp := (List.pairwise_flatMap.mp hi).2
  apply hp.imp_of_mem
  intro c d hc hd hcd v hv hdv
  have hne : c.original ≠ d.original := hcd _ (by simp [blockIds]) _ (by simp [blockIds])
  apply (List.disjoint_left.mp (h.vertices.disjoint hne))
  · simpa [h.original c hc] using hv
  · simpa [h.original d hd] using hdv

lemma BlockView.skip_before {n b : ℕ} {s : Heap n b} {epoch : ℕ} {first : Bool}
    {pre post : List (Block n b)} {c : Block n b} {f : CellContents n b}
    (h : BlockView s epoch first (pre++c::post) f) (v : Fin n) (hv : v∈c.residual) :
    ∀ e ∈ pre, v ∉ e.residual := by
  have hp := (List.pairwise_append.mp h.separate).2.2
  intro e he heq
  exact hp e he c List.mem_cons_self v heq hv

lemma BlockView.original_companion_ne {n b : ℕ} {s : Heap n b} {epoch : ℕ} {first : Bool}
    {pre post : List (Block n b)} {c : Block n b} {f : CellContents n b}
    (h : BlockView s epoch first (pre++c::post) f) (d : Fin b)
    (hd : c.companion=some d) : c.original ≠ d := by
  have hi : (allBlockIds pre++blockIds c++allBlockIds post).Nodup := by
    simpa [allBlockIds,List.append_assoc] using h.ids
  have hc := (List.nodup_append.mp (List.nodup_append.mp hi).1).2.1
  simpa [blockIds,hd] using hc

lemma erase_nil_iff_size {n b : ℕ} {s : Heap n b} {epoch : ℕ} {first : Bool}
    {bs : List (Block n b)} {f : CellContents n b} (h : BlockView s epoch first bs f)
    (c : Block n b) (hc : c∈bs) (v : Fin n) (hv : v∈c.residual) :
    c.residual.erase v=[] ↔ s.size[c.original.val]=1 := by
  have he := List.length_erase_add_one hv
  have hs : s.size[c.original.val]=c.residual.length :=
    (h.vertices.size c.original).trans (congrArg List.length (h.original c hc))
  rw [← List.length_eq_zero_iff]
  omega

lemma erased_decomposition {n : ℕ} (xs : List (Fin n)) (v : Fin n) (hn : xs.Nodup) (hv : v∈xs) :
    ∃ pre post, xs=pre++v::post ∧ xs.erase v=pre++post := by
  obtain ⟨pre,post,hx⟩ := List.mem_iff_append.mp hv
  have hvp : v∉pre := by
    intro hm
    have hi := (List.nodup_append.mp (hx ▸ hn)).2.2
    exact hi v hm v List.mem_cons_self rfl
  exact ⟨pre,post,hx,by rw [hx,List.erase_append_right _ hvp,List.erase_cons_head]⟩

/-- Existing-companion case of the exact heap/ghost simulation. -/
theorem simulate_existing {n b : ℕ} {s : Heap n b} {epoch : ℕ} {first : Bool}
    {pre post : List (Block n b)} {c : Block n b} {f : CellContents n b}
    (h : BlockView s epoch first (pre++c::post) f) (v : Fin n) (d : Fin b)
    (hv : v∈c.residual) (hd : c.companion=some d) :
    BlockView (moveNeighbor s epoch first v).value epoch first (pre++c.advance v d::post)
      (Function.update (Function.update f c.original (c.residual.erase v)) d (c.moved++[v])) ∧
      (moveNeighbor s epoch first v).value.fresh = s.fresh := by
  have hc : c∈pre++c::post := by simp
  have hcd := h.original_companion_ne d hd
  have howner : s.owner[v.val]=some c.original :=
    (h.vertices.owner v c.original).mpr (by simpa [h.original c hc] using hv)
  obtain ⟨hs,hcomp⟩ := h.touched c hc d hd
  have heval := moveNeighbor_existing s epoch first v c.original d howner hs hcomp
  have hfr : (moveNeighbor s epoch first v).value.fresh = s.fresh := by
    rw [heval,appendVertex_fresh,removeVertex_fresh]
  have hghost : LexBFSLabeled.moveOne v (pre++c::post) s.fresh =
      some (pre++c.advance v d::post,s.fresh) := by
    rw [LexBFSLabeled.moveOne_skip_prefix v pre (c::post) s.fresh (h.skip_before v hv)]
    simp [LexBFSLabeled.moveOne,hv,hd]
  have haddr := LexBFSLabeled.moveOne_addresses v _ _ _ _ ⟨h.ids,h.allocated⟩ hghost
  obtain ⟨vp,vq,hdec,herase⟩ := erased_decomposition c.residual v
    (by simpa [h.original c hc] using h.vertices.nodup c.original) hv
  have hfcell : f c.original=vp++v::vq := (h.original c hc).trans hdec
  have hvertex := moveNeighbor_existing_view h.vertices epoch first v c.original d hcd
    vp vq hfcell hs hcomp
  rw [← herase,h.companion c hc d hd] at hvertex
  have hsize := erase_nil_iff_size h c hc v hv
  have hcells : CellView (moveNeighbor s epoch first v).value
      ((emitted first (pre++c.advance v d::post)).map Prod.fst) := by
    let left := (emitted first pre).map Prod.fst
    let right := (emitted first post).map Prod.fst
    have hold : CellView s (left++(if first then [d,c.original] else [c.original,d])++right) := by
      simpa only [emitted,LexBFSLabeled.emit_ids_frame,c.emit_ids_existing first v d (h.valid c hc) hd hv] using h.cells
    have hnew : (emitted first (pre++c.advance v d::post)).map Prod.fst =
        left++(if s.size[c.original.val]=1 then [d] else
          if first then [d,c.original] else [c.original,d])++right := by
      simp only [left,right,emitted,LexBFSLabeled.emit_ids_frame,c.advance_existing_ids first v d hd,hsize]
    rw [hnew]
    cases first
    · have hh : CellView s (left++c.original::d::right) := by simpa [List.append_assoc] using hold
      have hm := moveNeighbor_existing_order epoch false v c.original d left (d::right) hh howner hs hcomp
      by_cases hz : s.size[c.original.val]=1 <;> simpa [hz,List.append_assoc] using hm
    · have hh : CellView s ((left++[d])++c.original::right) := by simpa [List.append_assoc] using hold
      have hm := moveNeighbor_existing_order epoch true v c.original d (left++[d]) right hh howner hs hcomp
      by_cases hz : s.size[c.original.val]=1 <;> simpa [hz,List.append_assoc] using hm
  have hstamp : (moveNeighbor s epoch first v).value.stamp=s.stamp.set c.original.val epoch := by
    rw [heval,appendVertex_stamp,removeVertex_stamp,← hs]
    simp
  have htable : (moveNeighbor s epoch first v).value.companion=s.companion.set c.original.val (some d) := by
    rw [heval,appendVertex_companion,removeVertex_companion,← hcomp]
    simp
  refine ⟨h.advance v d (Or.inr hd) hcd hvertex hcells haddr.1 ?_ ?_ hstamp htable,hfr⟩
  · omega
  · rw [hfr]
    exact h.allocated d (by simp [allBlockIds,blockIds,hd])

end HiddenCircuits.DH.LexBFSPartition
