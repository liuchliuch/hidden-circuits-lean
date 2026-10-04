import HiddenCircuits.DH.LexBFSCellOrder

/-! Constant-time pivot and slice-size extraction refines the pure partition pop. -/
namespace HiddenCircuits.DH.LexBFSPartition
open LexBFSLinks

lemma pop_empty {n b : ℕ} {s : Heap n b} (h : CellView s []) :
    (pop s).value = (none,s) := by simp [pop,h.first]

lemma pop_nonempty {n b : ℕ} {s : Heap n b} {f : CellContents n b}
    {c : Fin b} {cs : List (Fin b)} (hv : VertexView s f) (ho : CellView s (c::cs))
    (v : Fin n) (vs : List (Fin n)) (hc : f c = v::vs) :
    (pop s).value = (some ⟨v,vs.length+1⟩,(removeVertex s c v).value) := by
  simp [pop,ho.first,hv.head c,hv.size c,hc]

lemma pop_vertexView {n b : ℕ} {s : Heap n b} {f : CellContents n b}
    {c : Fin b} {cs : List (Fin b)} (hv : VertexView s f) (ho : CellView s (c::cs))
    (v : Fin n) (vs : List (Fin n)) (hc : f c = v::vs) :
    VertexView (pop s).value.2 (Function.update f c vs) := by
  rw [pop_nonempty hv ho v vs hc]
  exact removeVertex_view hv c v [] vs hc

lemma pop_cellView {n b : ℕ} {s : Heap n b} {f : CellContents n b}
    {c : Fin b} {cs : List (Fin b)} (hv : VertexView s f) (ho : CellView s (c::cs))
    (v : Fin n) (vs : List (Fin n)) (hc : f c = v::vs) :
    CellView (pop s).value.2 (if vs = [] then cs else c::cs) := by
  rw [pop_nonempty hv ho v vs hc]
  have h := removeVertex_order [] cs c v ho
  simpa [hv.size c,hc,List.length_eq_zero_iff] using h

lemma map_update_outside {n b : ℕ} (f : CellContents n b) (c : Fin b) (xs : List (Fin n))
    (cs : List (Fin b)) (hc : c ∉ cs) : cs.map (Function.update f c xs) = cs.map f := by
  apply List.map_congr_left
  intro d hd
  have hdc : d ≠ c := by intro he; exact hc (he ▸ hd)
  simp [Function.update,hdc]

/-- The emitted pair uses exactly the selected cell's pre-pop cardinal. Updating its
stored integer costs one read; no selected slice is copied or traversed. -/
theorem pop_model {n b : ℕ} {s : Heap n b} {f : CellContents n b}
    {c : Fin b} {cs : List (Fin b)} (hv : VertexView s f) (ho : CellView s (c::cs))
    (v : Fin n) (vs : List (Fin n)) (hc : f c = v::vs) :
    LexBFSModel.pop ((c::cs).map f) =
      some (v,vs.length+1,
        (if vs = [] then cs else c::cs).map (Function.update f c vs)) := by
  have hmap := map_update_outside f c vs cs (List.nodup_cons.mp ho.nodup).1
  simp only [List.map_cons,hc,LexBFSModel.pop]
  by_cases hvs : vs = []
  · simp only [hvs] at hmap ⊢
    simp [LexBFSModel.nonemptyCell,hmap]
  · simp [hvs,LexBFSModel.nonemptyCell,hmap]

end HiddenCircuits.DH.LexBFSPartition
