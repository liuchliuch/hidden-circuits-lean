import HiddenCircuits.DH.LexBFSBlockView

/-! Exact pivot-boundary conversion between the canonical heap and row provenance blocks. -/
namespace HiddenCircuits.DH.LexBFSPartition
open LexBFSLinks
open LexBFSLabeled (Block)

def initialBlocks {n b : ℕ} (cs : List (Fin b)) (f : CellContents n b) : List (Block n b) :=
  cs.map (fun c => ⟨c,f c,none,[]⟩)

@[simp] lemma initialBlocks_ids {n b : ℕ} (cs : List (Fin b)) (f : CellContents n b) :
    allBlockIds (initialBlocks cs f) = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    change c::allBlockIds (initialBlocks cs f) = c::cs
    rw [ih]

lemma initialBlocks_emitted {n b : ℕ} (first : Bool) (cs : List (Fin b)) (f : CellContents n b)
    (hf : ∀ c ∈ cs, f c ≠ []) : emitted first (initialBlocks cs f) = cs.map (fun c => (c,f c)) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have ht := ih (fun d hd => hf d (List.mem_cons_of_mem _ hd))
    have hc := hf c List.mem_cons_self
    cases first <;> simpa [emitted,initialBlocks,Block.emit,LexBFSLabeled.namedCell,hc] using
      congrArg (List.cons (c,f c)) ht

lemma initialBlocks_clean {n b : ℕ} (cs : List (Fin b)) (f : CellContents n b) :
    ∀ c ∈ initialBlocks cs f, c.companion=none ∧ c.moved=[] := by
  intro c hc
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
  exact ⟨rfl,rfl⟩

lemma initialBlocks_sorted {n b : ℕ} {s : Heap n b} {cs : List (Fin b)} {f : CellContents n b}
    (h : Canonical s cs f) : ∀ c ∈ initialBlocks cs f, c.residual.Pairwise (· < ·) := by
  intro c hc
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
  exact h.sorted d

lemma initialBlocks_separate {n b : ℕ} {s : Heap n b} {cs : List (Fin b)} {f : CellContents n b}
    (h : Canonical s cs f) : LexBFSLabeled.Separate (initialBlocks cs f) := by
  rw [LexBFSLabeled.Separate,initialBlocks,List.pairwise_map]
  apply h.cells.nodup.imp
  intro c d hcd v hv
  exact fun hd => List.disjoint_left.mp (h.vertices.disjoint hcd) hv hd

/-- Beginning a row allocates no ghost/runtime companions: every table entry is stale. -/
theorem Canonical.blockView {n b : ℕ} {s : Heap n b} {cs : List (Fin b)} {f : CellContents n b}
    {epoch : ℕ} (h : Canonical s cs f) (hr : Ready s epoch) (first : Bool) :
    BlockView s epoch first (initialBlocks cs f) f := by
  have hn : ∀ c ∈ cs, f c≠[] := fun c hc => (h.support c).mp hc
  have he : (emitted first (initialBlocks cs f)).map Prod.fst = cs := by
    rw [initialBlocks_emitted first cs f hn,List.map_map]
    simp [Function.comp_def]
  constructor
  · exact h.vertices
  · simpa only [he] using h.cells
  · intro c hc
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    rfl
  · intro c hc d he
    have hz := (initialBlocks_clean cs f c hc).1
    simp [hz] at he
  · intro d hd
    rw [initialBlocks_ids] at hd
    by_contra hf
    exact hd ((h.support d).mpr hf)
  · simpa only [initialBlocks_ids] using h.cells.nodup
  · simpa only [initialBlocks_ids] using h.allocated
  · intro c hc
    have hh := initialBlocks_clean cs f c hc
    simp [Block.Valid,hh.1,hh.2]
  · intro c hc hz
    exact Nat.ne_of_lt (hr c.original)
  · intro c hc d he
    have hz := (initialBlocks_clean cs f c hc).1
    simp [hz] at he
  · intro d
    exact Nat.le_of_lt (hr d)

lemma emitted_id_mem {n b : ℕ} (first : Bool) (bs : List (Block n b)) (d : Fin b)
    (hd : d ∈ (emitted first bs).map Prod.fst) : d ∈ allBlockIds bs := by
  obtain ⟨⟨e,xs⟩,he,heq⟩ := List.mem_map.mp hd
  dsimp only at heq
  subst e
  obtain ⟨c,hc,hm⟩ := List.mem_flatMap.mp he
  apply List.mem_flatMap.mpr
  refine ⟨c,hc,(mem_blockIds c d).mpr ?_⟩
  rcases (mem_emit first c d xs).mp hm with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

/-- Completing the sparse row restores the canonical heap for the next pivot. -/
theorem BlockView.canonical {n b : ℕ} {s : Heap n b} {epoch : ℕ} {first : Bool}
    {bs : List (Block n b)} {f : CellContents n b} (h : BlockView s epoch first bs f)
    (hcap : s.fresh ≤ b)
    (hsort : ∀ c ∈ bs, c.residual.Pairwise (· < ·) ∧ c.moved.Pairwise (· < ·)) :
    Canonical s ((emitted first bs).map Prod.fst) f := by
  refine ⟨h.vertices,h.cells,h.support,?_,hcap,?_⟩
  · intro d hd
    exact h.allocated d (emitted_id_mem first bs d hd)
  · intro d
    by_cases hz : f d=[]
    · simp [hz]
    · obtain ⟨⟨e,xs⟩,he,heq⟩ := List.mem_map.mp ((h.support d).mpr hz)
      dsimp only at heq
      subst e
      obtain ⟨c,hc,hm⟩ := List.mem_flatMap.mp he
      rcases (mem_emit first c d xs).mp hm with ⟨rfl,rfl,_⟩ | ⟨hd,rfl,_⟩
      · rw [h.original c hc]
        exact (hsort c hc).1
      · rw [h.companion c hc d hd]
        exact (hsort c hc).2

lemma BlockView.ready_next {n b : ℕ} {s : Heap n b} {epoch : ℕ} {first : Bool}
    {bs : List (Block n b)} {f : CellContents n b} (h : BlockView s epoch first bs f) :
    Ready s (epoch+1) := fun d => Nat.lt_succ_of_le (h.stampBound d)

end HiddenCircuits.DH.LexBFSPartition
