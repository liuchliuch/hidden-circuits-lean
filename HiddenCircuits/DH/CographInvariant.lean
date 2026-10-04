import HiddenCircuits.DH.CographFamilyMatrix

/-! Proof invariant for recursive traversal of the two fixed global sweep trees. -/
namespace HiddenCircuits.DH
open SimpleGraph LexBFSModel
variable {V : Type*} {G : SimpleGraph V}

/-- Both fixed sweep streams contain the same current module root. The slices
may have extra vertices, but the extras have the proved complete/empty cuts. -/
structure PairedModule (G : SimpleGraph V) (normal complement : List (Event V))
    (M : Set V) (root : V) : Prop where
  module : GraphModule G M
  root_mem : root∈M
  normal_position : ∃past size tail, normal=past++⟨root,size⟩::tail ∧
    JoinEnvelope G M (profileSlice G (past.map Event.vertex) root)
  complement_position : ∃past size tail, complement=past++⟨root,size⟩::tail ∧
    UnionEnvelope G M (profileSlice G (past.map Event.vertex) root)

lemma profileSlice_nil (r : V) : profileSlice G [] r=Set.univ := by
  ext x; simp [profileSlice]

lemma sweep_cons (a : V → V → Bool) (s : Bool) (r : V) (rest : List V) :
    sweep a s (r::rest) = ⟨r,rest.length+1⟩::run a s rest.length (refine s (a r) (nonemptyCell rest)) := by
  simp [sweep,run,pop,nonemptyCell]

/-- Initial paired envelopes come from the actual first pivots of the two
sweeps; the whole input vertex set is an ordinary graph module. -/
theorem PairedModule.initial [DecidableRel G.Adj] (r : V) (rest : List V) :
    PairedModule G
      (sweep (fun a b => decide (G.Adj a b)) true (r::rest))
      (sweep (fun a b => decide (G.Adj a b)) false
        ((sweep (fun a b => decide (G.Adj a b)) true (r::rest)).map Event.vertex)) Set.univ r := by
  let a := fun u v => decide (G.Adj u v)
  let tailN := run a true rest.length (refine true (a r) (nonemptyCell rest))
  refine ⟨?_,Set.mem_univ _,?_,?_⟩
  · intro u hu v hv x hx; exact False.elim (hx (Set.mem_univ _))
  · refine ⟨[],rest.length+1,tailN,?_,?_⟩
    · exact sweep_cons a true r rest
    · rw [List.map_nil,profileSlice_nil]
      exact JoinEnvelope.refl Set.univ
  · refine ⟨[],(tailN.map Event.vertex).length+1,
      run a false (tailN.map Event.vertex).length
        (refine false (a r) (nonemptyCell (tailN.map Event.vertex))),?_,?_⟩
    · rw [sweep_cons a true r rest]
      exact sweep_cons a false r (tailN.map Event.vertex)
    · rw [List.map_nil,profileSlice_nil]
      exact UnionEnvelope.refl Set.univ

/-- A later designated occurrence splits the earlier root's tail. Event labels,
not their compact sizes, are the keys used to locate the same occurrence. -/
lemma event_split_after {events rootPast rootTail childPast childTail : List (Event V)}
    {root child : Event V} (hn : (events.map Event.vertex).Nodup)
    (hr : events=rootPast++root::rootTail) (hc : events=childPast++child::childTail)
    (hnot : child.vertex∉rootPast.map Event.vertex) (hne : child.vertex≠root.vertex) :
    ∃middle, rootTail=middle++child::childTail ∧ childPast=rootPast++root::middle := by
  have hm : child.vertex∈events.map Event.vertex := by simp [hc]
  rw [hr,List.map_append,List.map_cons] at hm
  have htail : child.vertex∈rootTail.map Event.vertex :=
    (List.mem_cons.mp ((List.mem_append.mp hm).resolve_left hnot)).resolve_left hne
  obtain ⟨e,he,hev⟩ := List.mem_map.mp htail
  obtain ⟨middle,tail,ht⟩ := List.mem_iff_append.mp he
  have he' : events=(rootPast++root::middle)++e::tail := by simp [hr,ht,List.append_assoc]
  obtain ⟨hbefore,heq,htail⟩ := event_split_unique hn hc he' hev.symm
  subst e; subst tail
  exact ⟨middle,ht,hbefore⟩

lemma PairedModule.normal_fresh {normal complement : List (Event V)} {M : Set V} {r : V}
    (h : PairedModule G normal complement M r) {past : List (Event V)} {size : ℕ} {tail : List (Event V)}
    (he : normal=past++⟨r,size⟩::tail) (hn : (normal.map Event.vertex).Nodup) :
    ∀v∈M, v∉past.map Event.vertex := by
  obtain ⟨past',size',tail',he',henv⟩ := h.normal_position
  obtain ⟨hp,_,_⟩ := event_split_unique hn he he' rfl
  intro v hv
  simpa only [hp] using (henv.1 hv).1

lemma PairedModule.complement_fresh {normal complement : List (Event V)} {M : Set V} {r : V}
    (h : PairedModule G normal complement M r) {past : List (Event V)} {size : ℕ} {tail : List (Event V)}
    (he : complement=past++⟨r,size⟩::tail) (hn : (complement.map Event.vertex).Nodup) :
    ∀v∈M, v∉past.map Event.vertex := by
  obtain ⟨past',size',tail',he',henv⟩ := h.complement_position
  obtain ⟨hp,_,_⟩ := event_split_unique hn he he' rfl
  intro v hv
  simpa only [hp] using (henv.1 hv).1

/-- A first normal profile-class representative inherits the full paired
invariant using the same two fixed global sweeps. -/
theorem PairedModule.normal_child [DecidableRel G.Adj] (hG : P4Free G)
    (tie : List V) (htie : tie.Nodup) (hall : ∀v, v∈tie)
    {M : Set V} {r x : V}
    (h : PairedModule G (sweep (fun a b => decide (G.Adj a b)) true tie)
      (sweep (fun a b => decide (G.Adj a b)) false
        ((sweep (fun a b => decide (G.Adj a b)) true tie).map Event.vertex)) M r)
    (hx : FirstProfileHead G M r (sweep (fun a b => decide (G.Adj a b)) true tie) x) :
    PairedModule G (sweep (fun a b => decide (G.Adj a b)) true tie)
      (sweep (fun a b => decide (G.Adj a b)) false
        ((sweep (fun a b => decide (G.Adj a b)) true tie).map Event.vertex))
      (relativePivotCell G M r x) x := by
  let normal := sweep (fun a b => decide (G.Adj a b)) true tie
  let other := sweep (fun a b => decide (G.Adj a b)) false (normal.map Event.vertex)
  let C := relativePivotCell G M r x
  have hpN := sweep_perm (fun a b => decide (G.Adj a b)) true tie
  have hnN : (normal.map Event.vertex).Nodup := hpN.nodup_iff.mpr htie
  have hcoverN : ∀v, v∈normal.map Event.vertex := fun v => hpN.mem_iff.mpr (hall v)
  have hpC := sweep_perm (fun a b => decide (G.Adj a b)) false (normal.map Event.vertex)
  have hnC : (other.map Event.vertex).Nodup := hpC.nodup_iff.mpr hnN
  have hcoverC : ∀v, v∈other.map Event.vertex := fun v => hpC.mem_iff.mpr (hcoverN v)
  obtain ⟨hxM,hxN,bn,⟨y,sxn⟩,an,hfullN,hxy,hfreshN⟩ := hx
  dsimp only at hxy
  subst y
  have hC : GraphModule G C := hG.relativePivotCell_module h.module r x
  have hxC : x∈C := ⟨hxM,mem_pivotCell_self hxN⟩
  obtain ⟨ec,hec,hecx⟩ := List.mem_map.mp (hcoverC x)
  obtain ⟨bc,⟨y,sxc⟩,ac,hfullC,hyC,hfreshC⟩ :=
    exists_first_event_in_set other C ⟨ec,hec,hecx ▸ hxC⟩
  have heq : y=x := hC.two_sweep_first_eq tie htie hall bn ⟨x,sxn⟩ an hfullN
    bc ⟨y,sxc⟩ ac hfullC hxC hyC
    (by intro e he heC; exact hfreshN e.vertex heC (List.mem_map.mpr ⟨e,he,rfl⟩)) hfreshC
  subst y
  obtain ⟨pn,sn,tn,hpn,henvN⟩ := h.normal_position
  obtain ⟨pc,sc,tc,hpc,henvC⟩ := h.complement_position
  obtain ⟨mn,htn,hbn⟩ := event_split_after hnN hpn hfullN (henvN.1 hxM).1 hxN.1
  obtain ⟨mc,htc,hbc⟩ := event_split_after hnC hpc hfullC (henvC.1 hxM).1 hxN.1
  have hfull : normal=pn++⟨r,sn⟩::mn++⟨x,sxn⟩::an := by simpa only [hbn,List.append_assoc] using hfullN
  have hfN : ∀v∈C, v∉(pn++⟨r,sn⟩::mn).map Event.vertex := by simpa only [←hbn] using hfreshN
  have hfC : ∀v∈C, v∉pc.map Event.vertex++r::mc.map Event.vertex := by
    intro v hv hm
    have hm' : v∈bc.map Event.vertex := by simpa [hbc] using hm
    obtain ⟨e,he,hev⟩ := List.mem_map.mp hm'
    exact hfreshC e he (hev ▸ hv)
  obtain ⟨hmodule,hjoin,hunion⟩ := hG.normal_envelopes_child tie htie hall pn ⟨r,sn⟩ mn ⟨x,sxn⟩ an
    hfull h.module h.root_mem hxM hxN henvN (pc.map Event.vertex) (mc.map Event.vertex) henvC hfN hfC
  refine ⟨hmodule,hxC,⟨bn,sxn,an,hfullN,?_⟩,⟨bc,sxc,ac,hfullC,?_⟩⟩
  · simpa only [hbn] using hjoin
  · simpa only [hbc,List.map_append,List.map_cons] using hunion

/-- First complementary profile classes inherit the same paired invariant;
root agreement still refers to the original two sweeps, not a third sweep. -/
theorem PairedModule.complement_child [DecidableRel G.Adj] (hG : P4Free G)
    (tie : List V) (htie : tie.Nodup) (hall : ∀v, v∈tie)
    {M : Set V} {r x : V}
    (h : PairedModule G (sweep (fun a b => decide (G.Adj a b)) true tie)
      (sweep (fun a b => decide (G.Adj a b)) false
        ((sweep (fun a b => decide (G.Adj a b)) true tie).map Event.vertex)) M r)
    (hx : FirstProfileHead Gᶜ M r
      (sweep (fun a b => decide (G.Adj a b)) false
        ((sweep (fun a b => decide (G.Adj a b)) true tie).map Event.vertex)) x) :
    PairedModule G (sweep (fun a b => decide (G.Adj a b)) true tie)
      (sweep (fun a b => decide (G.Adj a b)) false
        ((sweep (fun a b => decide (G.Adj a b)) true tie).map Event.vertex))
      (relativePivotCell Gᶜ M r x) x := by
  classical
  let normal := sweep (fun a b => decide (G.Adj a b)) true tie
  let other := sweep (fun a b => decide (G.Adj a b)) false (normal.map Event.vertex)
  let C := relativePivotCell Gᶜ M r x
  have hpN := sweep_perm (fun a b => decide (G.Adj a b)) true tie
  have hnN : (normal.map Event.vertex).Nodup := hpN.nodup_iff.mpr htie
  have hcoverN : ∀v, v∈normal.map Event.vertex := fun v => hpN.mem_iff.mpr (hall v)
  have hpC := sweep_perm (fun a b => decide (G.Adj a b)) false (normal.map Event.vertex)
  have hnC : (other.map Event.vertex).Nodup := hpC.nodup_iff.mpr hnN
  obtain ⟨hxM,hxN,bc,⟨y,sxc⟩,ac,hfullC,hxy,hfreshC⟩ := hx
  dsimp only at hxy
  subst y
  have hC : GraphModule G C := graphModule_compl_iff.mp (hG.compl.relativePivotCell_module h.module.compl r x)
  have hxC : x∈C := ⟨hxM,mem_pivotCell_self hxN⟩
  have hadj : G.Adj r x := by simpa only [nonneighbors_compl,mem_neighborSet] using hxN
  obtain ⟨en,hen,henx⟩ := List.mem_map.mp (hcoverN x)
  obtain ⟨bn,⟨y,sxn⟩,an,hfullN,hyC,hfreshN⟩ :=
    exists_first_event_in_set normal C ⟨en,hen,henx ▸ hxC⟩
  have heq : x=y := hC.two_sweep_first_eq tie htie hall bn ⟨y,sxn⟩ an hfullN
    bc ⟨x,sxc⟩ ac hfullC hyC hxC hfreshN
    (by intro e he heC; exact hfreshC e.vertex heC (List.mem_map.mpr ⟨e,he,rfl⟩))
  subst y
  obtain ⟨pn,sn,tn,hpn,henvN⟩ := h.normal_position
  obtain ⟨pc,sc,tc,hpc,henvC⟩ := h.complement_position
  obtain ⟨mn,htn,hbn⟩ := event_split_after hnN hpn hfullN (henvN.1 hxM).1 hxN.1
  obtain ⟨mc,htc,hbc⟩ := event_split_after hnC hpc hfullC (henvC.1 hxM).1 hxN.1
  have hfull : other=pc++⟨r,sc⟩::mc++⟨x,sxc⟩::ac := by
    simpa only [hbc,List.append_assoc] using hfullC
  have hfC : ∀v∈C, v∉(pc++⟨r,sc⟩::mc).map Event.vertex := by simpa only [←hbc] using hfreshC
  have hfN : ∀v∈C, v∉pn.map Event.vertex++r::mn.map Event.vertex := by
    intro v hv hm
    have hm' : v∈bn.map Event.vertex := by simpa [hbn] using hm
    obtain ⟨e,he,hev⟩ := List.mem_map.mp hm'
    exact hfreshN e he (hev ▸ hv)
  obtain ⟨hmodule,hunion,hjoin⟩ := hG.complement_envelopes_child (normal.map Event.vertex) hnN hcoverN
    pc ⟨r,sc⟩ mc ⟨x,sxc⟩ ac hfull h.module h.root_mem hxM hadj henvC
    (pn.map Event.vertex) (mn.map Event.vertex) henvN hfC hfN
  refine ⟨hmodule,hxC,⟨bn,sxn,an,hfullN,?_⟩,⟨bc,sxc,ac,hfullC,?_⟩⟩
  · simpa only [hbn,List.map_append,List.map_cons] using hjoin
  · simpa only [hbc] using hunion

/-- Every recursive profile cell is genuinely smaller than its parent module. -/
lemma relativePivotCell_card_lt [Finite V] {M : Set V} {r x : V} (hr : r∈M) :
    (relativePivotCell G M r x).ncard<M.ncard := by
  apply Set.ncard_lt_ncard (ht := Set.toFinite M)
  refine Set.ssubset_iff_subset_ne.mpr ⟨Set.inter_subset_left,?_⟩
  intro he
  have hrC : r∈relativePivotCell G M r x := he.symm ▸ hr
  exact hrC.2.1.1 rfl

end HiddenCircuits.DH
