import HiddenCircuits.DH.LexBFSMove
import HiddenCircuits.DH.LexBFSPop
import HiddenCircuits.DH.LexBFSInitialize
import HiddenCircuits.DH.LexBFSResources

/-! Canonical heap invariants at pivot boundaries. -/
namespace HiddenCircuits.DH.LexBFSPartition
open LexBFSLinks

/-- All live cells, and only live cells, occur in the linked cell order. Every cell
is in original rank order; inactive slots have empty ghost contents. -/
structure Canonical {n b : ℕ} (s : Heap n b) (cs : List (Fin b)) (f : CellContents n b) : Prop where
  vertices : VertexView s f
  cells : CellView s cs
  support : ∀ c, c ∈ cs ↔ f c ≠ []
  allocated : ∀ c ∈ cs, c.val < s.fresh
  capacity : s.fresh ≤ b
  sorted : ∀ c, (f c).Pairwise (· < ·)

/-- A new pivot uses a strictly later epoch than every earlier cell refinement. -/
def Ready {n b : ℕ} (s : Heap n b) (epoch : ℕ) : Prop :=
  ∀ c : Fin b, s.stamp[c.val] < epoch

lemma Canonical.empty_unused {n b : ℕ} {s : Heap n b} {cs : List (Fin b)} {f : CellContents n b}
    (h : Canonical s cs f) (c : Fin b) (hc : s.fresh ≤ c.val) : f c = [] := by
  by_contra hn
  have ha := h.allocated c ((h.support c).mpr hn)
  omega

lemma initialHeap_canonical (n b : ℕ) (hb : 0 < b) :
    Canonical (initialHeap n b hb).value (if n = 0 then [] else [⟨0,hb⟩])
      (initialContents n b hb) := by
  refine ⟨initialHeap_vertexView n b hb,initialHeap_cellView n b hb,?_,?_,?_,?_⟩
  · intro c
    rw [initialContents_support]
    by_cases hn : n = 0 <;> simp [hn]
  · intro c hc
    by_cases hn : n = 0
    · simp [hn] at hc
    · have he : c = ⟨0,hb⟩ := by simpa [hn] using hc
      subst c
      simp
  · simp; omega
  · intro c
    by_cases hc : c = ⟨0,hb⟩
    · subst c
      simp only [initialContents,Function.update_self]
      rw [List.finRange,List.pairwise_ofFn]
      exact fun i j hij => hij
    · simp [initialContents,Function.update,hc]

lemma initialHeap_ready (n b : ℕ) (hb : 0 < b) : Ready (initialHeap n b hb).value 1 := by
  intro c
  simp

/-- A constant-time pop preserves every canonical invariant on the remaining partition. -/
theorem pop_canonical {n b : ℕ} {s : Heap n b} {cs : List (Fin b)} {f : CellContents n b}
    {c : Fin b} (h : Canonical s (c::cs) f)
    (v : Fin n) (vs : List (Fin n)) (hc : f c = v::vs) :
    Canonical (pop s).value.2 (if vs = [] then cs else c::cs) (Function.update f c vs) := by
  refine ⟨pop_vertexView h.vertices h.cells v vs hc,
    pop_cellView h.vertices h.cells v vs hc,?_,?_,?_,?_⟩
  · intro d
    by_cases hd : d = c
    · subst d
      have hnot := (List.nodup_cons.mp h.cells.nodup).1
      by_cases he : vs = [] <;> simp [he,hnot]
    · have hm : d ∈ cs ↔ f d ≠ [] := by simpa [hd] using h.support d
      by_cases he : vs = [] <;> simpa [he,Function.update,hd] using hm
  · intro d hd
    have hm : d ∈ c::cs := by
      split_ifs at hd
      · exact List.mem_cons_of_mem _ hd
      · exact hd
    simpa using h.allocated d hm
  · simpa using h.capacity
  · intro d
    by_cases hd : d = c
    · subst d
      simpa [hc] using (h.sorted c).tail
    · simpa [Function.update,hd] using h.sorted d

lemma pop_ready {n b : ℕ} {s : Heap n b} {epoch : ℕ} (h : Ready s epoch) :
    Ready (pop s).value.2 epoch := by
  intro c
  unfold pop
  split
  · exact h c
  · split
    · exact h c
    · simpa only [Counted.value,removeVertex_stamp] using h c

end HiddenCircuits.DH.LexBFSPartition
