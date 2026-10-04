import HiddenCircuits.DH.SliceHeadBuckets
import HiddenCircuits.DH.CographExactChildren

/-! Exact correspondence between the literal stack/bucket output and chronological
`EventParent` pairs. No parent forest or graph certificate is supplied as input. -/
namespace HiddenCircuits.DH.SliceHeads
open LexBFSModel

/-- Inverting a split of the timestamped frame stream recovers the corresponding
split of the original events, including its exact prefix frames and position. -/
lemma framesFrom_split {V : Type*} (i : ℕ) (events : List (Event V))
    (front : List (Frame V)) (f : Frame V) (back : List (Frame V))
    (h : framesFrom i events = front++f::back) :
    ∃ before e after, events=before++e::after ∧ front=framesFrom i before ∧
      f=⟨e.vertex,i+before.length,i+before.length+e.sliceSize⟩ := by
  induction front generalizing i events with
  | nil =>
    cases events with
    | nil => simp [framesFrom] at h
    | cons e es =>
      simp only [framesFrom,List.nil_append,List.cons.injEq] at h
      exact ⟨[],e,es,rfl,rfl,by simpa using h.1.symm⟩
  | cons g front ih =>
    cases events with
    | nil => simp [framesFrom] at h
    | cons e es =>
      simp only [framesFrom,List.cons_append,List.cons.injEq] at h
      obtain ⟨before,c,after,he,hfront,hf⟩ := ih (i+1) es h.2
      refine ⟨e::before,c,after,by simp [he],?_,?_⟩
      · simp [framesFrom,hfront,h.1]
      · simpa [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hf

lemma IsParent.mem {V : Type*} {past : List (Frame V)} {f p : Frame V}
    (h : IsParent past f (some p)) : p∈past := by
  have hh := head_some_mem h.symm
  exact List.mem_reverse.mp (List.mem_filter.mp hh).1

lemma mem_parentEntries {n : ℕ} (ps : List (ParentEvent (Fin n))) (u v : Fin n) :
    (u,v)∈(parentEntries ps).1 ↔
      ∃ p∈ps, ∃ r, p.parent=some r ∧ r.vertex=u ∧ p.frame.vertex=v := by
  rw [parentEntries_values,List.mem_filterMap]
  constructor
  · rintro ⟨p,hp,he⟩
    obtain ⟨r,hr,he⟩ := Option.map_eq_some_iff.mp he
    exact ⟨p,hp,r,hr,congrArg Prod.fst he,congrArg Prod.snd he⟩
  · rintro ⟨p,hp,r,hr,hu,hv⟩
    exact ⟨p,hp,by simp [hr,hu,hv]⟩

/-- Recovered entries have genuine earlier parent events, at their literal chronological
positions. This implication needs only the already checked stack semantics. -/
theorem parentEntries_build_sound {n : ℕ} (events : List (Event (Fin n)))
    (hl : Laminar (framesFrom 0 events)) (u v : Fin n)
    (hm : (u,v)∈(parentEntries (build events).events).1) :
    ∃ past root middle child after,
      events=past++root::middle++child::after ∧ root.vertex=u ∧ child.vertex=v ∧
      HiddenCircuits.DH.EventParent past root middle child := by
  obtain ⟨p,hp,r,hpr,hru,hpv⟩ := (mem_parentEntries _ u v).mp hm
  obtain ⟨beforeOut,afterOut,hout⟩ := List.mem_iff_append.mp hp
  have hframes := scan_frames 0 events []
  change (build events).events.map ParentEvent.frame=framesFrom 0 events at hframes
  rw [hout,List.map_append,List.map_cons] at hframes
  obtain ⟨before,child,after,he,hbefore,hchild⟩ :=
    framesFrom_split 0 events (beforeOut.map ParentEvent.frame) p.frame
      (afterOut.map ParentEvent.frame) hframes.symm
  have hcorrect := build_parent_correct events hl
  rw [hout] at hcorrect
  have his := hcorrect.at_split
  simp only [List.nil_append,hbefore,hpr] at his
  have hrmem := his.mem
  obtain ⟨past,root,middle,hbef,hr⟩ := (mem_framesFrom 0 before r).mp hrmem
  refine ⟨past,root,middle,child,after,?_,?_,?_,?_⟩
  · simpa [hbef,List.append_assoc] using he
  · simpa [hr] using hru
  · simpa [hchild] using hpv
  · unfold HiddenCircuits.DH.EventParent
    have hfpast : framesFrom 0 before =
        framesFrom 0 past++r::framesFrom (past.length+1) middle := by
      rw [hbef,framesFrom_append]
      simp [framesFrom,hr,Nat.add_assoc]
    rw [hfpast,hchild,hr] at his
    simpa [hbef,List.length_append,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using his

/-- Splitting the input stream has the same effect as continuing the literal stack
scan from the prefix's resulting stack. -/
lemma scan_append_stack {V : Type*} (i : ℕ) (before after : List (Event V)) (stack : List (Frame V)) :
    (scan i (before++after) stack).stack =
      (scan (i+before.length) after (scan i before stack).stack).stack := by
  induction before generalizing i stack with
  | nil => simp [scan]
  | cons e es ih =>
    simpa [scan,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      ih (i+1) (⟨e.vertex,i,i+e.sliceSize⟩::(trim i stack).1)

lemma scan_append_events {V : Type*} (i : ℕ) (before after : List (Event V)) (stack : List (Frame V)) :
    (scan i (before++after) stack).events = (scan i before stack).events ++
      (scan (i+before.length) after (scan i before stack).stack).events := by
  induction before generalizing i stack with
  | nil => simp [scan]
  | cons e es ih =>
    simpa [scan,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      congrArg (List.cons (ParentEvent.mk ⟨e.vertex,i,i+e.sliceSize⟩ (trim i stack).1.head?))
        (ih (i+1) (⟨e.vertex,i,i+e.sliceSize⟩::(trim i stack).1))

/-- Every semantic chronological event-parent pair is emitted by the actual parent
entry traversal after the one-pass stack construction. -/
theorem parentEntries_build_complete {n : ℕ} (events : List (Event (Fin n)))
    (hl : Laminar (framesFrom 0 events))
    (past : List (Event (Fin n))) (root : Event (Fin n)) (middle : List (Event (Fin n)))
    (child : Event (Fin n)) (after : List (Event (Fin n)))
    (he : events=past++root::middle++child::after)
    (hparent : HiddenCircuits.DH.EventParent past root middle child) :
    (root.vertex,child.vertex)∈(parentEntries (build events).events).1 := by
  let before := past++root::middle
  let initialScan := scan 0 before []
  let p : Frame (Fin n) := ⟨root.vertex,past.length,past.length+root.sliceSize⟩
  let f : Frame (Fin n) := ⟨child.vertex,before.length,before.length+child.sliceSize⟩
  let pe : ParentEvent (Fin n) := ⟨f,(trim before.length initialScan.stack).1.head?⟩
  let tail := (scan (before.length+1) after (f::(trim before.length initialScan.stack).1)).events
  have hout : (build events).events=initialScan.events++pe::tail := by
    have he' : events=before++child::after := by simpa [before,List.append_assoc] using he
    rw [he']
    change (scan 0 (before++child::after) []).events=_
    rw [scan_append_events]
    simp only [Nat.zero_add]
    rfl
  have hframes : initialScan.events.map ParentEvent.frame=framesFrom 0 before := scan_frames 0 before []
  have hcorrect := build_parent_correct events hl
  rw [hout] at hcorrect
  have his := hcorrect.at_split
  simp only [List.nil_append,hframes] at his
  have hfpast : framesFrom 0 before = framesFrom 0 past++p::framesFrom (past.length+1) middle := by
    simp [before,framesFrom_append,framesFrom,p,Nat.add_assoc]
  have hpar : IsParent (framesFrom 0 before) f (some p) := by
    rw [hfpast]
    simpa [HiddenCircuits.DH.EventParent,before,p,f,List.length_append,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hparent
  have hpe : pe.parent=some p := his.trans hpar.symm
  apply (mem_parentEntries _ root.vertex child.vertex).mpr
  exact ⟨pe,by rw [hout]; simp,p,hpe,rfl,rfl⟩

/-- Exact finite labels of the actual parent-entry list, valid for every laminar
compact event stream, without a vertex-uniqueness premise. -/
theorem parentEntries_build_iff {n : ℕ} (events : List (Event (Fin n)))
    (hl : Laminar (framesFrom 0 events)) (u v : Fin n) :
    (u,v)∈(parentEntries (build events).events).1 ↔
      ∃ past root middle child after,
        events=past++root::middle++child::after ∧ root.vertex=u ∧ child.vertex=v ∧
        HiddenCircuits.DH.EventParent past root middle child := by
  constructor
  · exact parentEntries_build_sound events hl u v
  · rintro ⟨past,root,middle,child,after,he,hu,hv,hp⟩
    simpa [hu,hv] using parentEntries_build_complete events hl past root middle child after he hp

/-- Ordinary and complement sweep outputs therefore supply exactly the chronological
`EventParent` pairs used by the cotree semantics. -/
theorem parentEntries_sweep_iff {n : ℕ} (a : Fin n → Fin n → Bool) (s : Bool)
    (tie : List (Fin n)) (u v : Fin n) :
    (u,v)∈(parentEntries (build (sweep a s tie)).events).1 ↔
      ∃ past root middle child after,
        sweep a s tie=past++root::middle++child::after ∧ root.vertex=u ∧ child.vertex=v ∧
        HiddenCircuits.DH.EventParent past root middle child :=
  parentEntries_build_iff _ (sweep_laminar a s tie) u v

/-- Parent entries retain the actual child-visit order; filtering absent parents
never permutes the remaining event labels. -/
lemma parentEntries_child_sublist {n : ℕ} (ps : List (ParentEvent (Fin n))) :
    ((parentEntries ps).1.map Prod.snd).Sublist (ps.map (fun p=>p.frame.vertex)) := by
  induction ps with
  | nil => exact .refl _
  | cons p ps ih =>
    cases hp : p.parent with
    | none => simpa [parentEntries,hp] using ih.cons p.frame.vertex
    | some f => simpa [parentEntries,hp] using ih.cons₂ p.frame.vertex

/-- Chronology of the emitted parent edges is a proved subsequence property of
literal stack output, independently of interval laminarity. -/
theorem parentEntries_build_child_sublist {n : ℕ} (events : List (Event (Fin n))) :
    ((parentEntries (build events).events).1.map Prod.snd).Sublist (events.map Event.vertex) := by
  have h := parentEntries_child_sublist (build events).events
  simpa only [build,scan_vertices] using h

/-- Each stable parent bucket is an actual subsequence of the sweep order. -/
theorem childHeads_sublist {n : ℕ} (events : List (Event (Fin n))) (u : Fin n) :
    ((childHeads events).rows[u.val]).Sublist (events.map Event.vertex) := by
  change ((groupParents (build events).events).rows[u.val]).Sublist _
  rw [groupParents_get]
  exact (List.filter_sublist.map Prod.snd).trans (parentEntries_build_child_sublist events)

/-- Any strict profile/rank ordering on the sweep therefore restricts to every
actual child-head bucket, rather than a separately supplied child enumeration. -/
theorem childHeads_pairwise {n : ℕ} (events : List (Event (Fin n))) (u : Fin n)
    (R : Fin n → Fin n → Prop) (h : (events.map Event.vertex).Pairwise R) :
    ((childHeads events).rows[u.val]).Pairwise R := h.sublist (childHeads_sublist events u)

/-- Duplicate-free sweep output gives duplicate-free actual child arrays. -/
theorem childHeads_nodup {n : ℕ} (events : List (Event (Fin n))) (u : Fin n)
    (h : (events.map Event.vertex).Nodup) : ((childHeads events).rows[u.val]).Nodup :=
  h.sublist (childHeads_sublist events u)

/-- The grouped array has the same exact chronological parent relation as the
ungrouped executable incidence list. -/
theorem childHeads_sweep_mem_iff {n : ℕ} (a : Fin n → Fin n → Bool) (s : Bool)
    (tie : List (Fin n)) (u v : Fin n) :
    v∈(childHeads (sweep a s tie)).rows[u.val] ↔
      ∃ past root middle child after,
        sweep a s tie=past++root::middle++child::after ∧ root.vertex=u ∧ child.vertex=v ∧
        HiddenCircuits.DH.EventParent past root middle child := by
  change v∈(groupParents (build (sweep a s tie)).events).rows[u.val] ↔ _
  rw [groupParents_get]
  have he : v∈(((parentEntries (build (sweep a s tie)).events).1.filter
      (fun p=>p.1==u)).map Prod.snd) ↔
      (u,v)∈(parentEntries (build (sweep a s tie)).events).1 := by
    constructor
    · intro hv
      obtain ⟨⟨x,y⟩,hm,he⟩ := List.mem_map.mp hv
      have hx : x=u := by simpa using (List.mem_filter.mp hm).2
      subst x
      dsimp only at he
      subst y
      exact (List.mem_filter.mp hm).1
    · intro hm
      exact List.mem_map.mpr ⟨(u,v),List.mem_filter.mpr ⟨hm,by simp⟩,rfl⟩
  rw [he,parentEntries_sweep_iff]

/-- Across all parents together, an actual child label is emitted at most once.
This is the sparse head-row charging invariant used by common-profile counting. -/
theorem parentEntries_build_heads_nodup {n : ℕ} (events : List (Event (Fin n)))
    (h : (events.map Event.vertex).Nodup) :
    ((parentEntries (build events).events).1.map Prod.snd).Nodup :=
  h.sublist (parentEntries_build_child_sublist events)

theorem parentEntries_sweep_heads_nodup {n : ℕ} (a : Fin n → Fin n → Bool) (s : Bool)
    (tie : List (Fin n)) (hn : tie.Nodup) :
    ((parentEntries (build (sweep a s tie)).events).1.map Prod.snd).Nodup :=
  parentEntries_build_heads_nodup _ ((sweep_perm a s tie).nodup_iff.mpr hn)

end HiddenCircuits.DH.SliceHeads
