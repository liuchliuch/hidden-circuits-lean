import HiddenCircuits.DH.CographSlices
import HiddenCircuits.DH.LexBFSSemantics

/-! Exact graph meaning of compact LexBFS event slices on P4-free graphs. -/
namespace HiddenCircuits.DH
open SimpleGraph LexBFSModel
variable {V : Type*} {G : SimpleGraph V}

lemma prefers_graph_equal [DecidableRel G.Adj] (s : Bool) (z x y : V) :
    prefers (fun a b => decide (G.Adj a b)) s z x =
      prefers (fun a b => decide (G.Adj a b)) s z y ↔ (G.Adj z x ↔ G.Adj z y) := by
  cases s <;> by_cases hx : G.Adj z x <;> by_cases hy : G.Adj z y <;>
    simp [prefers,hx,hy]

lemma suffix_mem_iff_not_prefix {past rest : List V} (hn : (past++rest).Nodup)
    (hall : ∀ v, v∈past++rest) (v : V) : v∈rest ↔ v∉past := by
  have hd := (List.nodup_append.mp hn).2.2
  constructor
  · intro h hp; exact hd v hp v h rfl
  · intro h
    exact (List.mem_append.mp (hall v)).resolve_left h

/-- The recorded interval is precisely the unselected graph-profile class. This
is obtained from the actual two sweep evaluator, not a supplied slice certificate. -/
theorem sweep_event_slice_graph [DecidableRel G.Adj] (s : Bool) (tie : List V)
    (htie : tie.Nodup) (hall : ∀v, v∈tie)
    (before : List (Event V)) (e : Event V) (after : List (Event V))
    (he : sweep (fun a b => decide (G.Adj a b)) s tie = before++e::after) :
    {v | v∈((e::after).map Event.vertex).take e.sliceSize} =
      profileSlice G (before.map Event.vertex) e.vertex := by
  have hp := sweep_perm (fun a b => decide (G.Adj a b)) s tie
  rw [he,List.map_append] at hp
  have hn := hp.nodup_iff.mpr htie
  have htotal : ∀v, v∈before.map Event.vertex ++ (e::after).map Event.vertex :=
    fun v => hp.mem_iff.mpr (hall v)
  have hs := sweep_slices (fun a b => decide (G.Adj a b)) s tie
  rw [he] at hs
  have hc := hs.drop_prefix
  simp only [List.nil_append] at hc
  ext v
  change v∈((e::after).map Event.vertex).take e.sliceSize ↔
    v∉before.map Event.vertex ∧ _
  rw [hc.2.2.1 v]
  rw [suffix_mem_iff_not_prefix hn htotal]
  apply and_congr Iff.rfl
  constructor
  · intro h z hz
    exact ((prefers_graph_equal s z e.vertex v).mp (h z hz)).symm
  · intro h z hz
    exact (prefers_graph_equal s z e.vertex v).mpr (h z hz).symm

/-- Every untouched nonneighbor profile class is represented by exactly one
whole recorded slice once the initial pivot's neighborhood has been visited. -/
theorem P4Free.sweep_event_pivotCell [DecidableRel G.Adj] (hG : P4Free G)
    (s : Bool) (tie : List V) (htie : tie.Nodup) (hall : ∀v, v∈tie)
    (before : List (Event V)) (e : Event V) (after : List (Event V))
    (he : sweep (fun a b => decide (G.Adj a b)) s tie = before++e::after)
    (r : V) (hx : e.vertex∈nonneighbors G r) (hr : r∈before.map Event.vertex)
    (hneighbors : ∀z, G.Adj r z → z∈before.map Event.vertex)
    (hfresh : ∀y∈pivotCell G r e.vertex, y∉before.map Event.vertex) :
    {v | v∈((e::after).map Event.vertex).take e.sliceSize} = pivotCell G r e.vertex := by
  rw [sweep_event_slice_graph s tie htie hall before e after he]
  exact hG.profileSlice_eq_pivotCell hx _ hr hneighbors hfresh

/-- Lexicographic priority orders distinct nonneighbor classes by decreasing
literal pivot profile, once the pivot-neighbor prefix is complete. -/
theorem P4Free.pivotProfile_order_of_priority [DecidableRel G.Adj] (hG : P4Free G)
    {r x y : V} (hx : x∈nonneighbors G r) (hy : y∈nonneighbors G r)
    (front back : List V) (hfront : ∀z∈front, z=r ∨ G.Adj r z)
    (hcover : ∀z, G.Adj r z → z∈front)
    (hp : SameProfile (prefers (fun a b => decide (G.Adj a b)) true) (front++back) x y ∨
      Ahead (prefers (fun a b => decide (G.Adj a b)) true) (front++back) x y) :
    pivotProfile G r y ⊆ pivotProfile G r x := by
  classical
  by_contra hnot
  have hsub : pivotProfile G r x ⊆ pivotProfile G r y :=
    (hG.pivotProfiles_nested hx hy).resolve_right hnot
  obtain ⟨z,hzy,hzx⟩ : ∃z∈pivotProfile G r y, z∉pivotProfile G r x := by
    exact Set.not_subset.mp hnot
  have hzx' : ¬G.Adj x z := fun h => hzx ⟨hzy.1,h⟩
  have hz : z∈front := hcover z hzy.1
  have hpzx : prefers (fun a b => decide (G.Adj a b)) true z x = false := by
    simp [prefers,show ¬G.Adj z x from fun h => hzx' h.symm]
  have hpzy : prefers (fun a b => decide (G.Adj a b)) true z y = true := by
    simp [prefers,hzy.2.symm]
  rcases hp with hp | hp
  · have he := hp z (List.mem_append_left _ hz)
    rw [hpzx,hpzy] at he
    contradiction
  · obtain ⟨before,after,hfrontEq⟩ := List.mem_iff_append.mp hz
    rw [hfrontEq,List.append_assoc] at hp
    obtain ⟨w,hw,hwx,hwy⟩ := hp.witness_before before hpzx hpzy
    have hwfront : w∈front := by rw [hfrontEq]; exact List.mem_append_left _ hw
    have hwx' : G.Adj w x := by simpa [prefers] using hwx
    have hwy' : ¬G.Adj w y := by simpa [prefers] using hwy
    rcases hfront w hwfront with rfl | hrw
    · exact hx.2 hwx'
    · exact hwy' (hsub ⟨hrw,hwx'.symm⟩).2.symm

/-- Preferred vertices precede unpreferred ones inside any equal-prefix cell,
not only for the first root of the whole graph. -/
lemma LexBFSModel.FourPoint.relative_preferred {prefer : V → V → Bool}
    {order before middle between after : List V} {r x y : V}
    (h : FourPoint prefer order)
    (he : order = before++r::middle++x::between++y::after)
    (hx : SameProfile prefer before r x) (hy : SameProfile prefer before r y)
    (hry : prefer r y=true) : prefer r x=true := by
  by_cases hrx : prefer r x=true
  · exact hrx
  · have hrx' : prefer r x=false := by simpa using hrx
    obtain ⟨w,hw,hwx,hwy⟩ := h before r middle x between y after he hry hrx'
    have heq := (hx w hw).symm.trans (hy w hw)
    rw [hwx,hwy] at heq
    contradiction

/-- The first occurrence in a nonempty covered set, used only in correctness
proofs; runtime roots are already supplied by the actual sweep events. -/
lemma exists_first_event_in_set (events : List (Event V)) (M : Set V)
    (h : ∃e∈events, e.vertex∈M) :
    ∃before e after, events=before++e::after ∧ e.vertex∈M ∧
      ∀b∈before, b.vertex∉M := by
  induction events with
  | nil => simpa using h
  | cons e es ih =>
    by_cases he : e.vertex∈M
    · exact ⟨[],e,es,rfl,he,by simp⟩
    · have hex : ∃b∈es, b.vertex∈M := by
        obtain ⟨b,hb,hbM⟩ := h
        rcases List.mem_cons.mp hb with rfl | hb
        · exact False.elim (he hbM)
        · exact ⟨b,hb,hbM⟩
      obtain ⟨before,b,after,hes,hbM,hprev⟩ := ih hex
      refine ⟨e::before,b,after,by simp [hes],hbM,?_⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact he
      · exact hprev c hc

lemma mem_take_at_split {α : Type*} [DecidableEq α] (before : List α) (x : α) (after : List α)
    (hn : (before++x::after).Nodup) (k : ℕ) :
    x∈(before++x::after).take k ↔ before.length<k := by
  have hx : x∉before := by
    intro hx
    exact (List.nodup_append.mp hn).2.2 x hx x List.mem_cons_self rfl
  rw [List.mem_take_iff_idxOf_lt (by simp),List.idxOf_append_of_notMem hx]
  simp

/-- Numeric containment in a compact event interval is exactly graph-profile
membership for every later event, linking the stack parent semantics to modules. -/
theorem sweep_interval_contains_iff [DecidableRel G.Adj] (s : Bool) (tie : List V)
    (htie : tie.Nodup) (hall : ∀v, v∈tie)
    (before : List (Event V)) (e : Event V) (middle : List (Event V))
    (f : Event V) (after : List (Event V))
    (he : sweep (fun a b => decide (G.Adj a b)) s tie = before++e::middle++f::after) :
    before.length+1+middle.length < before.length+e.sliceSize ↔
      f.vertex∈profileSlice G (before.map Event.vertex) e.vertex := by
  classical
  have hs := sweep_event_slice_graph s tie htie hall before e (middle++f::after)
    (by simpa [List.append_assoc] using he)
  rw [←hs]
  change before.length+1+middle.length < before.length+e.sliceSize ↔
    f.vertex∈((e::middle++f::after).map Event.vertex).take e.sliceSize
  have hp := sweep_perm (fun a b => decide (G.Adj a b)) s tie
  rw [he] at hp
  have hn := hp.nodup_iff.mpr htie
  simp only [List.map_append,List.map_cons] at hn
  have hn' : (before.map Event.vertex ++ e.vertex::(middle.map Event.vertex ++ f.vertex::after.map Event.vertex)).Nodup := by
    simpa only [List.append_assoc] using hn
  have hns := (List.nodup_append.mp hn').2.1
  have hm := mem_take_at_split (e.vertex::middle.map Event.vertex) f.vertex
    (after.map Event.vertex) hns e.sliceSize
  have hnum : before.length+1+middle.length < before.length+e.sliceSize ↔
      (e.vertex::middle.map Event.vertex).length < e.sliceSize := by
    simp only [List.length_cons,List.length_map]
    omega
  rw [hnum]
  simpa only [List.map_append,List.map_cons,List.cons_append] using hm.symm

/-- Within any recorded slice, every preferred vertex has already been visited
when a nonpreferred child is reached. This holds for both sweep directions. -/
theorem sweep_slice_preferred_before (a : V → V → Bool) (s : Bool) (tie : List V)
    (before : List (Event V)) (r : Event V) (middle : List (Event V))
    (x : Event V) (after : List (Event V))
    (he : sweep a s tie=before++r::middle++x::after)
    (hx : x.vertex∈((r::middle++x::after).map Event.vertex).take r.sliceSize)
    (hn : prefers a s r.vertex x.vertex=false)
    (z : V) (hz : z∈((r::middle++x::after).map Event.vertex).take r.sliceSize)
    (hp : prefers a s r.vertex z=true) : z∈(before++r::middle).map Event.vertex := by
  have hs := sweep_slices a s tie
  have he' : sweep a s tie=before++r::(middle++x::after) := by simpa [List.append_assoc] using he
  rw [he'] at hs
  have hc := hs.drop_prefix
  simp only [List.nil_append] at hc
  have hxprof := (hc.2.2.1 x.vertex).mp hx |>.2
  have hzall := (hc.2.2.1 z).mp hz
  have hmem := hzall.1
  simp only [List.map_append,List.map_cons,List.mem_cons,List.mem_append] at hmem
  rcases hmem with rfl | hzmid | hzx | hzafter
  · simp
  · simp [hzmid]
  · subst z; rw [hn] at hp; contradiction
  · obtain ⟨e,hem,hez⟩ := List.mem_map.mp hzafter
    obtain ⟨between,tail,hes⟩ := List.mem_iff_append.mp hem
    have horder := sweep_fourPoint a s tie
    have hf := horder.relative_preferred
      (before := before.map Event.vertex) (middle := middle.map Event.vertex)
      (between := between.map Event.vertex) (after := tail.map Event.vertex)
      (r := r.vertex) (x := x.vertex) (y := z)
      (by simp [he,hes,List.map_append,hez,List.append_assoc]) hxprof hzall.2 hp
    rw [hn] at hf
    contradiction

end HiddenCircuits.DH
