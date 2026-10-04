import HiddenCircuits.DH.LexBFSInvariant
import HiddenCircuits.DH.LexBFSLabeled

/-! Ghost provenance for sparse row refinement, tied to every actual heap array. -/
namespace HiddenCircuits.DH.LexBFSPartition
open LexBFSLinks
open LexBFSLabeled (Block namedCell)

/-- Retired original IDs stay in this proof-side provenance set; runtime storage does
not contain this list. Fresh companions are appended by the actual allocator. -/
def blockIds {n b : ℕ} (c : Block n b) : List (Fin b) := c.original::c.companion.toList

def allBlockIds {n b : ℕ} (bs : List (Block n b)) : List (Fin b) := bs.flatMap blockIds

def emitted {n b : ℕ} (first : Bool) (bs : List (Block n b)) : List (Fin b × List (Fin n)) :=
  bs.flatMap (Block.emit first)

/-- A row's provenance records exact array values, not assumed gate/graph correctness.
Epoch equality identifies a companion by one direct array lookup. -/
structure BlockView {n b : ℕ} (s : Heap n b) (epoch : ℕ) (first : Bool)
    (bs : List (Block n b)) (f : CellContents n b) : Prop where
  vertices : VertexView s f
  cells : CellView s ((emitted first bs).map Prod.fst)
  original : ∀ c ∈ bs, f c.original = c.residual
  companion : ∀ c ∈ bs, ∀ d, c.companion = some d → f d = c.moved
  outside : ∀ d, d ∉ allBlockIds bs → f d = []
  ids : (allBlockIds bs).Nodup
  allocated : ∀ d ∈ allBlockIds bs, d.val < s.fresh
  valid : ∀ c ∈ bs, c.Valid
  untouched : ∀ c ∈ bs, c.companion = none → s.stamp[c.original.val] ≠ epoch
  touched : ∀ c ∈ bs, ∀ d, c.companion = some d →
    s.stamp[c.original.val] = epoch ∧ s.companion[c.original.val] = some d
  stampBound : ∀ d : Fin b, s.stamp[d.val] ≤ epoch

lemma mem_blockIds {n b : ℕ} (c : Block n b) (d : Fin b) :
    d ∈ blockIds c ↔ d = c.original ∨ c.companion = some d := by
  simp [blockIds,Option.mem_toList]

lemma mem_namedCell {n b : ℕ} (c : Fin b) (xs : List (Fin n)) (d : Fin b) (ys : List (Fin n)) :
    (d,ys) ∈ namedCell c xs ↔ d=c ∧ ys=xs ∧ xs≠[] := by
  by_cases hx : xs=[] <;> simp [namedCell,hx,and_assoc]

lemma mem_emit {n b : ℕ} (first : Bool) (c : Block n b) (d : Fin b) (ys : List (Fin n)) :
    (d,ys) ∈ c.emit first ↔
      (d=c.original ∧ ys=c.residual ∧ c.residual≠[]) ∨
      (c.companion=some d ∧ ys=c.moved ∧ c.moved≠[]) := by
  cases hc : c.companion <;> cases first <;>
    simp [Block.emit,hc,mem_namedCell,or_comm,and_left_comm,and_assoc,eq_comm]

lemma BlockView.emitted_entry {n b : ℕ} {s : Heap n b} {epoch : ℕ} {first : Bool}
    {bs : List (Block n b)} {f : CellContents n b} (h : BlockView s epoch first bs f)
    {d : Fin b} {xs : List (Fin n)} (hm : (d,xs) ∈ emitted first bs) : f d=xs ∧ xs≠[] := by
  obtain ⟨c,hc,hm⟩ := List.mem_flatMap.mp hm
  rcases (mem_emit first c d xs).mp hm with ⟨rfl,rfl,hn⟩ | ⟨hd,rfl,hn⟩
  · exact ⟨h.original c hc,hn⟩
  · exact ⟨h.companion c hc d hd,hn⟩

lemma BlockView.emitted_values {n b : ℕ} {s : Heap n b} {epoch : ℕ} {first : Bool}
    {bs : List (Block n b)} {f : CellContents n b} (h : BlockView s epoch first bs f) :
    ((emitted first bs).map Prod.fst).map f = (emitted first bs).map Prod.snd := by
  rw [List.map_map]
  apply List.map_congr_left
  intro e he
  exact (h.emitted_entry he).1

lemma BlockView.support {n b : ℕ} {s : Heap n b} {epoch : ℕ} {first : Bool}
    {bs : List (Block n b)} {f : CellContents n b} (h : BlockView s epoch first bs f)
    (d : Fin b) : d ∈ (emitted first bs).map Prod.fst ↔ f d≠[] := by
  constructor
  · intro hd
    obtain ⟨⟨c,xs⟩,he,hh⟩ := List.mem_map.mp hd
    dsimp only at hh
    subst c
    obtain ⟨hf,hn⟩ := h.emitted_entry he
    simpa [hf] using hn
  · intro hd
    have hi : d ∈ allBlockIds bs := by by_contra hn; exact hd (h.outside d hn)
    obtain ⟨c,hc,hi⟩ := List.mem_flatMap.mp hi
    rcases (mem_blockIds c d).mp hi with rfl | hi
    · apply List.mem_map.mpr
      refine ⟨(c.original,c.residual),List.mem_flatMap.mpr ⟨c,hc,?_⟩,rfl⟩
      apply (mem_emit first c c.original c.residual).mpr
      exact Or.inl ⟨rfl,rfl,by simpa [h.original c hc] using hd⟩
    · apply List.mem_map.mpr
      refine ⟨(d,c.moved),List.mem_flatMap.mpr ⟨c,hc,?_⟩,rfl⟩
      apply (mem_emit first c d c.moved).mpr
      exact Or.inr ⟨hi,rfl,by simpa [h.companion c hc d hi] using hd⟩

/-- Every live owner names either its original block or that block's actual companion. -/
lemma BlockView.owner_cases {n b : ℕ} {s : Heap n b} {epoch : ℕ} {first : Bool}
    {bs : List (Block n b)} {f : CellContents n b} (h : BlockView s epoch first bs f)
    (v : Fin n) (d : Fin b) (hv : s.owner[v.val] = some d) :
    ∃ c ∈ bs, (d=c.original ∧ v∈c.residual) ∨ (c.companion=some d ∧ v∈c.moved) := by
  have hm := (h.vertices.owner v d).mp hv
  have hn : f d≠[] := List.ne_nil_of_mem hm
  have hi : d ∈ allBlockIds bs := by by_contra hi; exact hn (h.outside d hi)
  obtain ⟨c,hc,hi⟩ := List.mem_flatMap.mp hi
  refine ⟨c,hc,?_⟩
  rcases (mem_blockIds c d).mp hi with rfl | hi
  · exact Or.inl ⟨rfl,by simpa [h.original c hc] using hm⟩
  · exact Or.inr ⟨hi,by simpa [h.companion c hc d hi] using hm⟩

end HiddenCircuits.DH.LexBFSPartition
