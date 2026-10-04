import HiddenCircuits.DH.CographHeadFamilies
import HiddenCircuits.DH.SortProfileHeads

/-! Literal profile-family invariants derived from the executable head arrays. -/
namespace HiddenCircuits.DH
open SimpleGraph LexBFSModel
variable {V : Type*} {G : SimpleGraph V}

/-- One representative of each relative nonneighbor profile class, with no
pruning, cotree, or order theorem included in the data specification. -/
structure ProfileFamily (G : SimpleGraph V) (M : Set V) (r : V) (heads : List V) : Prop where
  members : ∀x∈heads, x∈M ∧ x∈nonneighbors G r
  covers : ∀x∈M, x∈nonneighbors G r → ∃y∈heads, pivotProfile G r x=pivotProfile G r y
  classes_nodup : (heads.map (pivotProfile G r)).Nodup

lemma profileFamily_of_first_iff (M : Set V) (r : V) (events : List (Event V)) (heads : List V)
    (hn : heads.Nodup) (hall : ∀v∈M, v∈events.map Event.vertex)
    (hspec : ∀v, v∈heads ↔ FirstProfileHead G M r events v) : ProfileFamily G M r heads := by
  refine ⟨?_,?_,?_⟩
  · intro x hx
    have h := (hspec x).mp hx
    exact ⟨h.1,h.2.1⟩
  · intro x hxM hxN
    obtain ⟨y,hy,he⟩ := exists_firstProfileHead events M r x hall hxM hxN
    exact ⟨y,(hspec y).mpr hy,he⟩
  · rw [List.Nodup,List.pairwise_map]
    apply hn.pairwise_of_forall_ne
    intro x hx y hy hne heq
    exact hne (((hspec x).mp hx).eq_of_profile_eq ((hspec y).mp hy) heq)

lemma ProfileFamily.perm {M : Set V} {r : V} {heads sorted : List V}
    (h : ProfileFamily G M r heads) (hp : sorted.Perm heads) : ProfileFamily G M r sorted where
  members x hx := h.members x (hp.mem_iff.mp hx)
  covers x hx hn := by
    obtain ⟨y,hy,he⟩ := h.covers x hx hn
    exact ⟨y,hp.mem_iff.mpr hy,he⟩
  classes_nodup := (hp.map _).nodup_iff.mpr h.classes_nodup

lemma ProfileFamily.heads_nodup {M : Set V} {r : V} {heads : List V}
    (h : ProfileFamily G M r heads) : heads.Nodup := List.Nodup.of_map _ h.classes_nodup

lemma ProfileFamily.strict_order [Finite V] {M : Set V} {r : V} {heads : List V}
    (h : ProfileFamily G M r heads) (hG : P4Free G)
    (hs : heads.Pairwise (fun x y => (pivotProfile G r y).ncard≤(pivotProfile G r x).ncard)) :
    heads.Pairwise (fun x y => pivotProfile G r y ⊂ pivotProfile G r x) := by
  have hd : heads.Pairwise (fun x y => pivotProfile G r x ≠ pivotProfile G r y) := by
    simpa only [List.Nodup,List.pairwise_map] using h.classes_nodup
  apply (hs.and hd).imp_of_mem
  intro x y hx hy hxy
  exact hG.pivotProfile_strict_of_card (h.members x hx).2 (h.members y hy).2 hxy.1 hxy.2

/-- Normal head-array correctness includes complete class coverage and uniqueness. -/
theorem P4Free.normal_head_family {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hG : P4Free G) (rows : Vector (List (Fin n)) n) (hr : LinearBuckets.Adjacency.Represents G rows)
    (tie : List (Fin n)) (htie : tie.Nodup) (hall : ∀v, v∈tie)
    (past : List (Event (Fin n))) (root : Event (Fin n)) (tail : List (Event (Fin n)))
    (he : sweep (fun a b => decide (G.Adj a b)) true tie=past++root::tail)
    {M : Set (Fin n)} (hM : GraphModule G M) (hrM : root.vertex∈M)
    (henv : JoinEnvelope G M (profileSlice G (past.map Event.vertex) root.vertex)) :
    ProfileFamily G M root.vertex
      (NonpreferredHeads.construct rows true (sweep (fun a b => decide (G.Adj a b)) true tie)).rows[root.vertex.val] := by
  have hp := sweep_perm (fun a b => decide (G.Adj a b)) true tie
  apply profileFamily_of_first_iff M root.vertex (sweep (fun a b => decide (G.Adj a b)) true tie)
  · exact (hp.nodup_iff.mpr htie).sublist
      (NonpreferredHeads.construct_child_sublist G rows hr true _ root.vertex)
  · intro v _; exact hp.mem_iff.mpr (hall v)
  · exact hG.normal_heads_iff rows hr tie htie hall past root tail he hM hrM henv

/-- The opposite original-row sweep has the symmetric complete family theorem. -/
theorem P4Free.complement_head_family {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hG : P4Free G) (rows : Vector (List (Fin n)) n) (hr : LinearBuckets.Adjacency.Represents G rows)
    (tie : List (Fin n)) (htie : tie.Nodup) (hall : ∀v, v∈tie)
    (past : List (Event (Fin n))) (root : Event (Fin n)) (tail : List (Event (Fin n)))
    (he : sweep (fun a b => decide (G.Adj a b)) false tie=past++root::tail)
    {M : Set (Fin n)} (hM : GraphModule G M) (hrM : root.vertex∈M)
    (henv : UnionEnvelope G M (profileSlice G (past.map Event.vertex) root.vertex)) :
    ProfileFamily Gᶜ M root.vertex
      (NonpreferredHeads.construct rows false (sweep (fun a b => decide (G.Adj a b)) false tie)).rows[root.vertex.val] := by
  have hp := sweep_perm (fun a b => decide (G.Adj a b)) false tie
  apply profileFamily_of_first_iff M root.vertex (sweep (fun a b => decide (G.Adj a b)) false tie)
  · exact (hp.nodup_iff.mpr htie).sublist
      (NonpreferredHeads.construct_child_sublist G rows hr false _ root.vertex)
  · intro v _; exact hp.mem_iff.mpr (hall v)
  · exact hG.complement_heads_iff rows hr tie htie hall past root tail he hM hrM henv

end HiddenCircuits.DH
