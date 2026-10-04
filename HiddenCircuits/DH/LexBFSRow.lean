import HiddenCircuits.DH.LexBFSSimulationNew
import HiddenCircuits.DH.LexBFSBlockBoundary

/-! Complete simulation of the sparse direct-pointer refinement loop. -/
namespace HiddenCircuits.DH.LexBFSPartition
open LexBFSLinks
open LexBFSLabeled (Block)

lemma ghost_untouched {n b : ℕ} (v : Fin n) (bs : List (Block n b)) (fresh : ℕ)
    (h : ∀ c∈bs, v∉c.residual) : LexBFSLabeled.moveOne v bs fresh = some (bs,fresh) := by
  induction bs with
  | nil => rfl
  | cons c cs ih => simp [LexBFSLabeled.moveOne,h c List.mem_cons_self,
      ih (fun d hd => h d (List.mem_cons_of_mem _ hd))]

/-- One row occurrence is either already selected, or belongs to its unique original
block. A duplicate-free row never moves a current companion vertex for a second time. -/
theorem simulate_one {n b : ℕ} {s : Heap n b} {epoch : ℕ} {first : Bool}
    {bs : List (Block n b)} {f : CellContents n b} (h : BlockView s epoch first bs f)
    (v : Fin n) (havoid : ∀ c∈bs, v∉c.moved) (hf : s.fresh < b) :
    ∃ ds f' fresh', LexBFSLabeled.moveOne v bs s.fresh = some (ds,fresh') ∧
      BlockView (moveNeighbor s epoch first v).value epoch first ds f' ∧
      (moveNeighbor s epoch first v).value.fresh = fresh' := by
  classical
  by_cases hex : ∃ c∈bs, v∈c.residual
  · obtain ⟨c,hc,hv⟩ := hex
    obtain ⟨pre,post,hbs⟩ := List.mem_iff_append.mp hc
    subst bs
    cases hd : c.companion with
    | none =>
      let d : Fin b := ⟨s.fresh,hf⟩
      have hs := simulate_new h v hv hd hf
      refine ⟨pre++c.advance v d::post,
        Function.update (Function.update f c.original (c.residual.erase v)) d (c.moved++[v]),
        s.fresh+1,?_,hs.1,hs.2⟩
      rw [LexBFSLabeled.moveOne_skip_prefix v pre (c::post) s.fresh (h.skip_before v hv)]
      simp [LexBFSLabeled.moveOne,hv,hd,hf,d]
    | some d =>
      have hs := simulate_existing h v d hv hd
      refine ⟨pre++c.advance v d::post,
        Function.update (Function.update f c.original (c.residual.erase v)) d (c.moved++[v]),
        s.fresh,?_,hs.1,hs.2⟩
      rw [LexBFSLabeled.moveOne_skip_prefix v pre (c::post) s.fresh (h.skip_before v hv)]
      simp [LexBFSLabeled.moveOne,hv,hd]
  · have hn : ∀ c∈bs, v∉c.residual := by simpa using hex
    have howner : s.owner[v.val] = none := by
      cases ho : s.owner[v.val] with
      | none => rfl
      | some d =>
        obtain ⟨c,hc,hh⟩ := h.owner_cases v d ho
        rcases hh with ⟨_,hh⟩ | ⟨_,hh⟩
        · exact False.elim (hn c hc hh)
        · exact False.elim (havoid c hc hh)
    have he := moveNeighbor_absent s epoch first v howner
    exact ⟨bs,f,s.fresh,ghost_untouched v bs s.fresh hn,he.symm ▸ h,congrArg Heap.fresh he⟩

lemma ghost_moved_avoid {n b : ℕ} (v w : Fin n) (bs ds : List (Block n b))
    (fresh fresh' : ℕ) (hs : LexBFSLabeled.Separate bs)
    (havoid : ∀ c∈bs, w∉c.moved) (hwv : w≠v)
    (h : LexBFSLabeled.moveOne v bs fresh = some (ds,fresh')) : ∀ d∈ds, w∉d.moved := by
  intro d hd
  have hm : (d.residual,d.moved) ∈ ds.map (fun c => (c.residual,c.moved)) :=
    List.mem_map.mpr ⟨d,hd,rfl⟩
  rw [LexBFSLabeled.moveOne_pairs v bs ds fresh fresh' hs h] at hm
  obtain ⟨c,hc,he⟩ := List.mem_map.mp hm
  have he' := congrArg Prod.snd he
  dsimp only at he'
  rw [← he']
  by_cases hv : v∈c.residual <;> simp [LexBFSSparse.moveRow,hv,havoid c hc,hwv]

/-- Every counted pointer-loop state has exact labeled provenance. No list-level work
is executed: this theorem only relates the literal array loop to its ghost specification. -/
theorem simulate_row {n b : ℕ} {s : Heap n b} {epoch : ℕ} {first : Bool}
    {bs : List (Block n b)} {f : CellContents n b} (h : BlockView s epoch first bs f)
    (row : List (Fin n)) (hn : row.Nodup) (havoid : ∀ v∈row, ∀ c∈bs, v∉c.moved)
    (hcap : s.fresh+row.length≤b) :
    ∃ ds f' fresh', LexBFSLabeled.moveAll row bs s.fresh = some (ds,fresh') ∧
      BlockView (refineRow epoch first row s).value epoch first ds f' ∧
      (refineRow epoch first row s).value.fresh = fresh' := by
  induction row generalizing s bs f with
  | nil => exact ⟨bs,f,s.fresh,rfl,h,rfl⟩
  | cons v row ih =>
    have hf : s.fresh<b := by simp only [List.length_cons] at hcap; omega
    obtain ⟨mid,fmid,next,hone,hmid,hfresh⟩ := simulate_one h v (havoid v List.mem_cons_self) hf
    have htail : ∀ w∈row, ∀ c∈mid, w∉c.moved := by
      intro w hw
      have hwv : w≠v := fun he => (List.nodup_cons.mp hn).1 (he ▸ hw)
      exact ghost_moved_avoid v w bs mid s.fresh next h.separate
        (havoid w (List.mem_cons_of_mem _ hw)) hwv hone
    have hroom : (moveNeighbor s epoch first v).value.fresh+row.length≤b := by
      have hh := (moveNeighbor_fresh s epoch first v).2
      simp only [List.length_cons] at hcap
      omega
    obtain ⟨ds,f',fresh',hrest,hfinal,hfinalfresh⟩ := ih hmid (List.nodup_cons.mp hn).2 htail hroom
    refine ⟨ds,f',fresh',?_,hfinal,hfinalfresh⟩
    simp only [LexBFSLabeled.moveAll,hone,Option.bind_some]
    simpa [hfresh] using hrest

/-- The actual sparse pointer loop is exactly stable partition refinement, for ordinary
and complement sweeps alike, with a fresh canonical heap and the next epoch ready. -/
theorem refineRow_correct {n b : ℕ} {s : Heap n b} {cs : List (Fin b)} {f : CellContents n b}
    (h : Canonical s cs f) (epoch : ℕ) (first : Bool) (row : List (Fin n))
    (hready : Ready s epoch) (hrow : row.Pairwise (· < ·)) (hcap : s.fresh+row.length≤b) :
    ∃ cs' f', Canonical (refineRow epoch first row s).value cs' f' ∧
      Ready (refineRow epoch first row s).value (epoch+1) ∧
      cs'.map f' = LexBFSModel.refine first (fun v=>decide (v∈row)) (cs.map f) := by
  have hi := h.blockView hready first
  obtain ⟨ds,f',fresh',hghost,hfinal,hfresh⟩ := simulate_row hi row hrow.nodup
    (by intro v hv c hc; simp [(initialBlocks_clean cs f c hc).2]) hcap
  have hsep := initialBlocks_separate h
  have hclean := initialBlocks_clean cs f
  have hsort := LexBFSLabeled.moveAll_sorted row (initialBlocks cs f) ds s.fresh fresh' hsep
    (fun c hc => (hclean c hc).2) hrow (initialBlocks_sorted h) hghost
  have hbound : (refineRow epoch first row s).value.fresh≤b :=
    (refineRow_fresh row s epoch first).2.trans hcap
  refine ⟨(emitted first ds).map Prod.fst,f',hfinal.canonical hbound hsort,hfinal.ready_next,?_⟩
  rw [hfinal.emitted_values]
  have he := LexBFSLabeled.moveAll_refine first row (initialBlocks cs f) ds s.fresh fresh'
    hsep hclean hrow (initialBlocks_sorted h) hghost
  simpa [emitted,initialBlocks,List.map_map,Function.comp_def] using he

end HiddenCircuits.DH.LexBFSPartition
