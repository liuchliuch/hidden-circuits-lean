import HiddenCircuits.DH.SliceHeadCorrespondence
import HiddenCircuits.DH.NonpreferredHeads
import HiddenCircuits.DH.CographRootAgreement

/-! Exact graph meaning of the computed nonpreferred-head families. -/
namespace HiddenCircuits.DH
open SimpleGraph LexBFSModel SliceHeads
variable {V : Type*} {G : SimpleGraph V}

/-- Distinct event labels make a designated vertex's chronological split unique,
including its compact slice length and its entire event prefix/suffix. -/
lemma event_split_unique {events before before' after after' : List (Event V)}
    {e e' : Event V} (hn : (events.map Event.vertex).Nodup)
    (h : events=before++e::after) (h' : events=before'++e'::after') (he : e.vertex=e'.vertex) :
    before=before' ∧ e=e' ∧ after=after' := by
  have hn' : (before.map Event.vertex++e.vertex::after.map Event.vertex).Nodup := by simpa [h] using hn
  have hnotBefore : e'.vertex∉before.map Event.vertex := by
    rw [←he]
    intro hm
    exact (List.nodup_append.mp hn').2.2 _ hm _ List.mem_cons_self rfl
  have hnotAfter : e'.vertex∉after.map Event.vertex := by
    rw [←he]
    exact (List.nodup_cons.mp (List.nodup_append.mp hn').2.1).1
  have hmap : before.map Event.vertex++e.vertex::after.map Event.vertex =
      before'.map Event.vertex++e'.vertex::after'.map Event.vertex := by
    simpa using congrArg (List.map Event.vertex) (h.symm.trans h')
  have hpre := (List.append_cons_inj_of_notMem hnotBefore hnotAfter).mp hmap |>.1
  have hlen : before.length=before'.length := by simpa using congrArg List.length hpre
  have hp := List.append_inj_left (h.symm.trans h') hlen
  have ht := List.append_inj_right (h.symm.trans h') hlen
  exact ⟨hp,(List.cons.inj ht).1,(List.cons.inj ht).2⟩

lemma NonpreferredHeads.construct_mem_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : LinearBuckets.Adjacency.Represents G rows)
    (s : Bool) (events : List (Event (Fin n))) (u v : Fin n) :
    v∈(construct rows s events).rows[u.val] ↔
      (u,v)∈(parentEntries (build events).events).1 ∧ (decide (G.Adj u v) != s)=true := by
  rw [construct_get G rows hr]
  constructor
  · intro hv
    obtain ⟨⟨x,y⟩,hm,he⟩ := List.mem_map.mp hv
    have hx : x=u := by simpa using (List.mem_filter.mp hm).2
    subst x
    dsimp only at he
    subst y
    exact ⟨(List.mem_filter.mp (List.mem_filter.mp hm).1).1,
      (List.mem_filter.mp (List.mem_filter.mp hm).1).2⟩
  · rintro ⟨hm,hp⟩
    exact List.mem_map.mpr ⟨(u,v),List.mem_filter.mpr
      ⟨List.mem_filter.mpr ⟨hm,hp⟩,by simp⟩,rfl⟩

lemma NonpreferredHeads.construct_sweep_mem_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : LinearBuckets.Adjacency.Represents G rows)
    (s : Bool) (tie : List (Fin n)) (u v : Fin n) :
    v∈(construct rows s (sweep (fun a b => decide (G.Adj a b)) s tie)).rows[u.val] ↔
      (∃past root middle child after,
        sweep (fun a b => decide (G.Adj a b)) s tie=past++root::middle++child::after ∧
          root.vertex=u ∧ child.vertex=v ∧ EventParent past root middle child) ∧
      (decide (G.Adj u v) != s)=true := by
  rw [construct_mem_iff G rows hr,parentEntries_sweep_iff]

/-- Use a fixed parent event rather than existentially renaming its occurrence. -/
lemma NonpreferredHeads.construct_fixed_parent_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : LinearBuckets.Adjacency.Represents G rows)
    (s : Bool) (tie : List (Fin n)) (htie : tie.Nodup)
    (past : List (Event (Fin n))) (root : Event (Fin n)) (tail : List (Event (Fin n)))
    (he : sweep (fun a b => decide (G.Adj a b)) s tie=past++root::tail) (v : Fin n) :
    v∈(construct rows s (sweep (fun a b => decide (G.Adj a b)) s tie)).rows[root.vertex.val] ↔
      (∃middle child after, tail=middle++child::after ∧ child.vertex=v ∧ EventParent past root middle child) ∧
        (decide (G.Adj root.vertex v) != s)=true := by
  rw [construct_sweep_mem_iff G rows hr]
  apply and_congr _ Iff.rfl
  constructor
  · rintro ⟨past',root',middle,child,after,hfull,hr',hc,hp⟩
    have hnd := (sweep_perm (fun a b => decide (G.Adj a b)) s tie).nodup_iff.mpr htie
    have hf : sweep (fun a b => decide (G.Adj a b)) s tie=past'++root'::(middle++child::after) := by
      simpa [List.append_assoc] using hfull
    obtain ⟨hpre,hrt,ht⟩ := event_split_unique hnd he hf hr'.symm
    subst past'; subst root'
    exact ⟨middle,child,after,ht,hc,hp⟩
  · rintro ⟨middle,child,after,ht,hc,hp⟩
    exact ⟨past,root,middle,child,after,by simp [he,ht,List.append_assoc],rfl,hc,hp⟩

/-- Literal first occurrence of one relative pivot-profile class. -/
def FirstProfileHead (G : SimpleGraph V) (M : Set V) (r : V)
    (events : List (Event V)) (v : V) : Prop :=
  v∈M ∧ v∈nonneighbors G r ∧ ∃before e after, events=before++e::after ∧ e.vertex=v ∧
    ∀x∈relativePivotCell G M r v, x∉before.map Event.vertex

lemma first_event_set_unique (events : List (Event V)) (C : Set V)
    {before before' after after' : List (Event V)} {e e' : Event V}
    (h : events=before++e::after) (h' : events=before'++e'::after')
    (he : e.vertex∈C) (he' : e'.vertex∈C)
    (hb : ∀x∈C, x∉before.map Event.vertex) (hb' : ∀x∈C, x∉before'.map Event.vertex) : e=e' := by
  classical
  have first (p : List (Event V)) (r : Event V) (q : List (Event V))
      (hh : events=p++r::q) (hr : r.vertex∈C) (hp : ∀x∈C, x∉p.map Event.vertex) :
      (events.filter (fun a => a.vertex∈C)).head?=some r := by
    have hn : p.filter (fun a => a.vertex∈C)=[] := List.filter_eq_nil_iff.mpr (by
      intro a ha hc
      exact hp a.vertex (by simpa using hc) (List.mem_map.mpr ⟨a,ha,rfl⟩))
    simp [hh,List.filter_append,hn,hr]
  exact Option.some.inj ((first _ _ _ h he hb).symm.trans (first _ _ _ h' he' hb'))

/-- The chronological parent predicate is precisely the first local profile
class representative, with no precomputed head-family certificate. -/
theorem P4Free.parentHead_iff_first [DecidableRel G.Adj] (hG : P4Free G)
    (tie : List V) (htie : tie.Nodup) (hall : ∀v, v∈tie)
    (past : List (Event V)) (root : Event V) (tail : List (Event V))
    (he : sweep (fun a b => decide (G.Adj a b)) true tie=past++root::tail)
    {M : Set V} (hM : GraphModule G M) (hrM : root.vertex∈M)
    (henv : JoinEnvelope G M (profileSlice G (past.map Event.vertex) root.vertex)) (v : V) :
    ((∃middle child after, tail=middle++child::after ∧ child.vertex=v ∧ EventParent past root middle child) ∧
      ¬G.Adj root.vertex v) ↔
      FirstProfileHead G M root.vertex (sweep (fun a b => decide (G.Adj a b)) true tie) v := by
  have hp := sweep_perm (fun a b => decide (G.Adj a b)) true tie
  have hnd := hp.nodup_iff.mpr htie
  have hnd' : (past.map Event.vertex++root.vertex::tail.map Event.vertex).Nodup := by
    simpa [he] using hnd
  have hrootnot : root.vertex∉tail.map Event.vertex :=
    (List.nodup_cons.mp (List.nodup_append.mp hnd').2.1).1
  constructor
  · rintro ⟨⟨middle,child,after,ht,hv,hpar⟩,hn⟩
    have hfull : sweep (fun a b => decide (G.Adj a b)) true tie=past++root::middle++child::after := by
      simp [he,ht,List.append_assoc]
    have hnc : ¬G.Adj root.vertex child.vertex := by simpa [hv] using hn
    have hs := (hG.normal_child_iff tie htie hall past root middle child after hfull hM hrM henv hnc).mp hpar
    have hvr : v≠root.vertex := by
      intro hvroot
      exact hrootnot (by simp [ht,hv,hvroot])
    refine ⟨hv ▸ hs.1,⟨hvr,hn⟩,past++root::middle,child,after,?_,hv,?_⟩
    · simpa [List.append_assoc] using hfull
    · simpa [hv] using hs.2
  · rintro ⟨hvM,hvN,before,e,after,hfull,hev,hfresh⟩
    have hvAll := hp.mem_iff.mpr (hall v)
    rw [he,List.map_append,List.map_cons] at hvAll
    have hvTail : v∈tail.map Event.vertex := by
      rcases List.mem_append.mp hvAll with h | h
      · exact False.elim ((henv.1 hvM).1 h)
      · exact (List.mem_cons.mp h).resolve_left hvN.1
    obtain ⟨child,hchild,hcv⟩ := List.mem_map.mp hvTail
    obtain ⟨middle,rest,ht⟩ := List.mem_iff_append.mp hchild
    have hfull' : sweep (fun a b => decide (G.Adj a b)) true tie=
        (past++root::middle)++child::rest := by simp [he,ht,List.append_assoc]
    obtain ⟨hb,_,_⟩ := event_split_unique hnd hfull hfull' (hev.trans hcv.symm)
    have hn : ¬G.Adj root.vertex child.vertex := by simpa [hcv] using hvN.2
    refine ⟨⟨middle,child,rest,ht,hcv,?_⟩,hvN.2⟩
    apply (hG.normal_child_iff tie htie hall past root middle child rest
      (by simpa [List.append_assoc] using hfull') hM hrM henv hn).mpr
    refine ⟨by simpa [hcv] using hvM,?_⟩
    simpa only [hcv,←hb] using hfresh

/-- Exact computed normal-head semantics at a module root. -/
theorem P4Free.normal_heads_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hG : P4Free G) (rows : Vector (List (Fin n)) n) (hr : LinearBuckets.Adjacency.Represents G rows)
    (tie : List (Fin n)) (htie : tie.Nodup) (hall : ∀v, v∈tie)
    (past : List (Event (Fin n))) (root : Event (Fin n)) (tail : List (Event (Fin n)))
    (he : sweep (fun a b => decide (G.Adj a b)) true tie=past++root::tail)
    {M : Set (Fin n)} (hM : GraphModule G M) (hrM : root.vertex∈M)
    (henv : JoinEnvelope G M (profileSlice G (past.map Event.vertex) root.vertex)) (v : Fin n) :
    v∈(NonpreferredHeads.construct rows true (sweep (fun a b => decide (G.Adj a b)) true tie)).rows[root.vertex.val] ↔
      FirstProfileHead G M root.vertex (sweep (fun a b => decide (G.Adj a b)) true tie) v := by
  rw [NonpreferredHeads.construct_fixed_parent_iff G rows hr true tie htie past root tail he]
  simpa using hG.parentHead_iff_first tie htie hall past root tail he hM hrM henv v

/-- Every nonempty local class has a first representative in the actual complete
event stream. No enumeration of equivalence classes is supplied. -/
lemma exists_firstProfileHead (events : List (Event V)) (M : Set V) (r x : V)
    (hall : ∀v∈M, v∈events.map Event.vertex) (hxM : x∈M) (hxN : x∈nonneighbors G r) :
    ∃y, FirstProfileHead G M r events y ∧ pivotProfile G r x=pivotProfile G r y := by
  let C := relativePivotCell G M r x
  have hxC : x∈C := ⟨hxM,mem_pivotCell_self hxN⟩
  obtain ⟨e,he,hex⟩ := List.mem_map.mp (hall x hxM)
  obtain ⟨before,y,after,hfull,hy,hbefore⟩ :=
    exists_first_event_in_set events C ⟨e,he,hex ▸ hxC⟩
  have hcells : relativePivotCell G M r y.vertex=C := by
    change M∩pivotCell G r y.vertex = M∩pivotCell G r x
    rw [pivotCell_eq_of_mem hy.2]
  refine ⟨y.vertex,⟨hy.1,hy.2.1,before,y,after,hfull,rfl,?_⟩,hy.2.2.symm⟩
  intro z hz hzmem
  obtain ⟨b,hb,hbz⟩ := List.mem_map.mp hzmem
  exact hbefore b hb (hbz ▸ (hcells ▸ hz))

/-- A profile class cannot contribute two different first representatives. -/
lemma FirstProfileHead.eq_of_profile_eq {M : Set V} {r u v : V} {events : List (Event V)}
    (hu : FirstProfileHead G M r events u) (hv : FirstProfileHead G M r events v)
    (he : pivotProfile G r u=pivotProfile G r v) : u=v := by
  obtain ⟨huM,huN,bu,eu,au,heu,hevU,hfu⟩ := hu
  obtain ⟨hvM,hvN,bv,ev,av,hev,hevV,hfv⟩ := hv
  let C := relativePivotCell G M r u
  have huC : eu.vertex∈C := by rw [hevU]; exact ⟨huM,mem_pivotCell_self huN⟩
  have hvC : ev.vertex∈C := by rw [hevV]; exact ⟨hvM,hvN,he.symm⟩
  have hCV : C=relativePivotCell G M r v := by
    ext z
    simp only [C,relativePivotCell,pivotCell,Set.mem_inter_iff,Set.mem_setOf_eq,he]
  have hfv' : ∀z∈C, z∉bv.map Event.vertex := by
    intro z hz; exact hfv z (hCV ▸ hz)
  have hE := first_event_set_unique events C heu hev huC hvC hfu hfv'
  exact hevU.symm.trans ((congrArg Event.vertex hE).trans hevV)

lemma NonpreferredHeads.construct_child_sublist {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : LinearBuckets.Adjacency.Represents G rows)
    (s : Bool) (events : List (Event (Fin n))) (r : Fin n) :
    ((construct rows s events).rows[r.val]).Sublist (events.map Event.vertex) := by
  rw [construct_get G rows hr]
  exact ((List.filter_sublist.trans List.filter_sublist).map Prod.snd).trans
    (parentEntries_build_child_sublist events)

/-- Exact computed complementary-head semantics, still using only original
adjacency rows and the verified off-diagonal complement sweep adapter. -/
theorem P4Free.complement_heads_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hG : P4Free G) (rows : Vector (List (Fin n)) n) (hr : LinearBuckets.Adjacency.Represents G rows)
    (tie : List (Fin n)) (htie : tie.Nodup) (hall : ∀v, v∈tie)
    (past : List (Event (Fin n))) (root : Event (Fin n)) (tail : List (Event (Fin n)))
    (he : sweep (fun a b => decide (G.Adj a b)) false tie=past++root::tail)
    {M : Set (Fin n)} (hM : GraphModule G M) (hrM : root.vertex∈M)
    (henv : UnionEnvelope G M (profileSlice G (past.map Event.vertex) root.vertex)) (v : Fin n) :
    v∈(NonpreferredHeads.construct rows false (sweep (fun a b => decide (G.Adj a b)) false tie)).rows[root.vertex.val] ↔
      FirstProfileHead Gᶜ M root.vertex (sweep (fun a b => decide (G.Adj a b)) false tie) v := by
  classical
  let P := ∃middle child after, tail=middle++child::after ∧ child.vertex=v ∧ EventParent past root middle child
  have hp := sweep_perm (fun a b => decide (G.Adj a b)) false tie
  have hn := hp.nodup_iff.mpr htie
  have hn' : (past.map Event.vertex++root.vertex::tail.map Event.vertex).Nodup := by simpa [he] using hn
  have hnot : root.vertex∉tail.map Event.vertex := (List.nodup_cons.mp (List.nodup_append.mp hn').2.1).1
  have hneq : P → root.vertex≠v := by
    rintro ⟨middle,child,after,ht,hv,_⟩ heq
    exact hnot (by simp [ht,hv,heq])
  have hc : (P ∧ G.Adj root.vertex v) ↔ (P ∧ ¬Gᶜ.Adj root.vertex v) := by
    constructor
    · rintro ⟨hP,hA⟩; exact ⟨hP,fun h => ((G.compl_adj _ _).mp h).2 hA⟩
    · rintro ⟨hP,hA⟩
      refine ⟨hP,?_⟩
      by_contra hnA
      exact hA ((G.compl_adj _ _).mpr ⟨hneq hP,hnA⟩)
  have he' : sweep (fun a b => decide (Gᶜ.Adj a b)) true tie=past++root::tail := by
    rw [←sweep_graph_complement G tie htie]
    exact he
  have henv' : JoinEnvelope Gᶜ M (profileSlice Gᶜ (past.map Event.vertex) root.vertex) := by
    rw [profileSlice_compl _ (henv.1 hrM).1]
    exact henv.compl
  rw [NonpreferredHeads.construct_fixed_parent_iff G rows hr false tie htie past root tail he]
  change (P ∧ (decide (G.Adj root.vertex v) != false)=true) ↔ _
  simp only [Bool.bne_false,decide_eq_true_eq]
  rw [hc]
  have h := hG.compl.parentHead_iff_first tie htie hall past root tail he' hM.compl hrM henv' v
  rw [←sweep_graph_complement G tie htie] at h
  exact h

end HiddenCircuits.DH
