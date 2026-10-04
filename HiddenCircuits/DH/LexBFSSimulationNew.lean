import HiddenCircuits.DH.LexBFSSimulation

namespace HiddenCircuits.DH.LexBFSPartition
open LexBFSLinks
open LexBFSLabeled (Block)

/-- First-touch allocation, with its literal fresh ID, simulates the labeled ghost step. -/
theorem simulate_new {n b : ℕ} {s : Heap n b} {epoch : ℕ} {first : Bool}
    {pre post : List (Block n b)} {c : Block n b} {f : CellContents n b}
    (h : BlockView s epoch first (pre++c::post) f) (v : Fin n)
    (hv : v∈c.residual) (hd : c.companion=none) (hf : s.fresh < b) :
    let d : Fin b := ⟨s.fresh,hf⟩
    BlockView (moveNeighbor s epoch first v).value epoch first (pre++c.advance v d::post)
      (Function.update (Function.update f c.original (c.residual.erase v)) d (c.moved++[v])) ∧
      (moveNeighbor s epoch first v).value.fresh = s.fresh+1 := by
  let d : Fin b := ⟨s.fresh,hf⟩
  have hc : c∈pre++c::post := by simp
  have hcn : c.original.val < s.fresh := h.allocated c.original (by simp [allBlockIds,blockIds])
  have hcd : c.original ≠ d := by intro he; have hh := congrArg Fin.val he; dsimp [d] at hh; omega
  have hdn : d ∉ allBlockIds (pre++c::post) := by
    intro hm
    have hh := h.allocated d hm
    exact (Nat.lt_irrefl s.fresh) hh
  have hempty : f d=[] := h.outside d hdn
  have hmoved : c.moved=[] := (h.valid c hc).mp hd
  have howner : s.owner[v.val]=some c.original :=
    (h.vertices.owner v c.original).mpr (by simpa [h.original c hc] using hv)
  have hs := h.untouched c hc hd
  have heval := moveNeighbor_new s epoch first v c.original howner hs hf
  have hfr : (moveNeighbor s epoch first v).value.fresh = s.fresh+1 := by
    rw [heval,appendVertex_fresh,removeVertex_fresh]
    simp [newCompanion,hf,d]
  have hghost : LexBFSLabeled.moveOne v (pre++c::post) s.fresh =
      some (pre++c.advance v d::post,s.fresh+1) := by
    rw [LexBFSLabeled.moveOne_skip_prefix v pre (c::post) s.fresh (h.skip_before v hv)]
    simp [LexBFSLabeled.moveOne,hv,hd,hf,d]
  have haddr := LexBFSLabeled.moveOne_addresses v _ _ _ _ ⟨h.ids,h.allocated⟩ hghost
  obtain ⟨vp,vq,hdec,herase⟩ := erased_decomposition c.residual v
    (by simpa [h.original c hc] using h.vertices.nodup c.original) hv
  have hfcell : f c.original=vp++v::vq := (h.original c hc).trans hdec
  have hvertex := moveNeighbor_new_view h.vertices epoch first v c.original
    vp vq hfcell hs hf hcd hempty
  rw [← herase] at hvertex
  have hsize := erase_nil_iff_size h c hc v hv
  have hcells : CellView (moveNeighbor s epoch first v).value
      ((emitted first (pre++c.advance v d::post)).map Prod.fst) := by
    let left := (emitted first pre).map Prod.fst
    let right := (emitted first post).map Prod.fst
    have hold : CellView s (left++c.original::right) := by
      simpa only [left,right,emitted,LexBFSLabeled.emit_ids_frame,
        c.emit_ids_new first v (h.valid c hc) hd hv,List.append_assoc,List.singleton_append] using h.cells
    have hnew : (emitted first (pre++c.advance v d::post)).map Prod.fst =
        left++(if s.size[c.original.val]=1 then [d] else
          if first then [d,c.original] else [c.original,d])++right := by
      simp only [left,right,emitted,LexBFSLabeled.emit_ids_frame,c.advance_new_ids first v d hd,hsize]
    have hdn' : d ∉ left++c.original::right := by
      intro hm
      have hh : f d≠[] := (h.support d).mp (by
        simpa only [left,right,emitted,LexBFSLabeled.emit_ids_frame,
          c.emit_ids_new first v (h.valid c hc) hd hv,List.append_assoc,List.singleton_append] using hm)
      exact hh hempty
    have hm := moveNeighbor_new_order epoch first v c.original left right hold howner hs hf hdn'
    rw [hnew]
    cases first <;> by_cases hz : s.size[c.original.val]=1 <;>
      simpa [hz,List.append_assoc,d] using hm
  have hstamp : (moveNeighbor s epoch first v).value.stamp=s.stamp.set c.original.val epoch := by
    rw [heval,appendVertex_stamp,removeVertex_stamp]
    simp [newCompanion,hf,d]
  have htable : (moveNeighbor s epoch first v).value.companion=s.companion.set c.original.val (some d) := by
    rw [heval,appendVertex_companion,removeVertex_companion]
    simp [newCompanion,hf,d]
  refine ⟨h.advance v d (Or.inl hd) hcd ?_ hcells haddr.1 ?_ ?_ hstamp htable,hfr⟩
  · simpa [hmoved,d] using hvertex
  · omega
  · rw [hfr]
    exact Nat.lt_succ_self _

end HiddenCircuits.DH.LexBFSPartition
