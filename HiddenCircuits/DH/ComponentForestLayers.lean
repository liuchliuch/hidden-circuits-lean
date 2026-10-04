import HiddenCircuits.DH.ComponentForest

/-! BFS distance invariants relative to the shared marks of earlier components.
Reachability is explicit, so disconnected and empty graphs need no certificates. -/
namespace HiddenCircuits.DH.ComponentForest
open SimpleGraph BreadthFirst
attribute [local instance] Classical.propDecidable

structure LayerInvariant {n : ℕ} (G : SimpleGraph (Fin n)) (r : Fin n)
    (base : Vector (Option ℕ) n) (level : ℕ) (marks : Vector (Option ℕ) n)
    (frontier : List (Fin n)) : Prop where
  base_none : ∀ v, G.Reachable r v → base[v.val]=none
  marks_eq : ∀ v, marks[v.val] = if G.Reachable r v ∧ G.dist r v≤level then some (G.dist r v) else base[v.val]
  frontier_eq : ∀ v, v∈frontier ↔ G.Reachable r v ∧ G.dist r v=level
  nodup : frontier.Nodup

lemma LayerInvariant.marks_none {n : ℕ} {G : SimpleGraph (Fin n)} {r : Fin n}
    {base : Vector (Option ℕ) n} {level : ℕ} {marks : Vector (Option ℕ) n} {frontier : List (Fin n)}
    (hi : LayerInvariant G r base level marks frontier) (v : Fin n) (hr : G.Reachable r v) :
    marks[v.val]=none ↔ level<G.dist r v := by
  rw [hi.marks_eq]
  simp [hr,hi.base_none v hr]

lemma LayerInvariant.new_iff {n : ℕ} {G : SimpleGraph (Fin n)} {r : Fin n}
    {base : Vector (Option ℕ) n} {level : ℕ} {marks : Vector (Option ℕ) n} {frontier : List (Fin n)}
    (hi : LayerInvariant G r base level marks frontier) (rows : Vector (List (Fin n)) n)
    (hr : LinearBuckets.Adjacency.Represents G rows) (y : Fin n) :
    (marks[y.val]=none ∧ ∃ v∈frontier, y∈rows[v.val]) ↔ G.Reachable r y ∧ G.dist r y=level+1 := by
  constructor
  · rintro ⟨hn,v,hv,hy⟩
    obtain ⟨hvR,hvd⟩ := (hi.frontier_eq v).mp hv
    have ha := (hr v y).mp hy
    have hyR := hvR.trans ha.reachable
    have hgt := (hi.marks_none y hyR).mp hn
    have hdist := ha.reachable.dist_triangle_right r
    rw [dist_eq_one_iff_adj.mpr ha] at hdist
    exact ⟨hyR,by omega⟩
  · rintro ⟨hyR,hy⟩
    obtain ⟨v,hv⟩ := predecessors_nonempty hyR (by omega)
    have hvR := hyR.trans hv.1.symm.reachable
    exact ⟨(hi.marks_none y hyR).mpr (by omega),v,
      (hi.frontier_eq v).mpr ⟨hvR,by have := hv.2;omega⟩,(hr v y).mpr hv.1⟩

lemma LayerInvariant.expand {n : ℕ} {G : SimpleGraph (Fin n)} {r : Fin n}
    {base : Vector (Option ℕ) n} {level : ℕ} {marks : Vector (Option ℕ) n} {frontier : List (Fin n)}
    (hi : LayerInvariant G r base level marks frontier) (rows : Vector (List (Fin n)) n)
    (hr : LinearBuckets.Adjacency.Represents G rows) :
    LayerInvariant G r base (level+1) (expand rows level frontier marks).marks (expand rows level frontier marks).next := by
  refine ⟨hi.base_none,?_,?_,expand_next_nodup rows level frontier marks⟩
  · intro y
    rw [expand_marks]
    by_cases hnew : marks[y.val]=none ∧ ∃v∈frontier, y∈rows[v.val]
    · obtain ⟨hyR,hy⟩ := (hi.new_iff rows hr y).mp hnew
      simp [hnew,hyR,hy]
    · rw [if_neg hnew,hi.marks_eq]
      by_cases hyR : G.Reachable r y
      · have hne : G.dist r y≠level+1 := fun h => hnew ((hi.new_iff rows hr y).mpr ⟨hyR,h⟩)
        by_cases hd : G.dist r y≤level
        · simp [hyR,hd,show G.dist r y≤level+1 by omega]
        · simp [hyR,hd,show ¬G.dist r y≤level+1 by omega]
      · simp [hyR]
  · intro y
    rw [expand_next]
    exact hi.new_iff rows hr y

lemma LayerInvariant.idle {n : ℕ} {G : SimpleGraph (Fin n)} {r : Fin n}
    {base : Vector (Option ℕ) n} {level : ℕ} {marks : Vector (Option ℕ) n}
    (hi : LayerInvariant G r base level marks []) (rows : Vector (List (Fin n)) n)
    (hr : LinearBuckets.Adjacency.Represents G rows) (fuel : ℕ) :
    LayerInvariant G r base (level+fuel) marks [] := by
  induction fuel with
  | zero => simpa using hi
  | succ fuel ih =>
    have h := ih.expand rows hr
    simpa [expand,neighborsFrom,discover,Nat.add_assoc] using h

lemma LayerInvariant.no_later {n : ℕ} {G : SimpleGraph (Fin n)} {r : Fin n}
    {base : Vector (Option ℕ) n} {level : ℕ} {marks : Vector (Option ℕ) n}
    (hi : LayerInvariant G r base level marks []) (rows : Vector (List (Fin n)) n)
    (hr : LinearBuckets.Adjacency.Represents G rows) (v : Fin n) (hv : G.Reachable r v) :
    G.dist r v<level := by
  by_contra h
  have hh := (hi.idle rows hr (G.dist r v-level)).frontier_eq v
  have he : level+(G.dist r v-level)=G.dist r v := by omega
  rw [he] at hh
  have := hh.mpr ⟨hv,rfl⟩
  simp at this

lemma explore_invariant {n : ℕ} {G : SimpleGraph (Fin n)}
    (rows : Vector (List (Fin n)) n) (hr : LinearBuckets.Adjacency.Represents G rows)
    (fuel level : ℕ) (r : Fin n) (base marks : Vector (Option ℕ) n) (frontier : List (Fin n))
    (hi : LayerInvariant G r base level marks frontier) :
    LayerInvariant G r base (level+fuel) (explore rows fuel level frontier marks).marks
      (explore rows fuel level frontier marks).frontier := by
  induction fuel generalizing level marks frontier with
  | zero => simpa [explore] using hi
  | succ fuel ih =>
    cases frontier with
    | nil => simpa [explore] using hi.idle rows hr (fuel+1)
    | cons v vs =>
      have h := ih (level+1) (expand rows level (v::vs) marks).marks (expand rows level (v::vs) marks).next
        (hi.expand rows hr)
      simpa [explore,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

lemma explore_members {n : ℕ} {G : SimpleGraph (Fin n)}
    (rows : Vector (List (Fin n)) n) (hr : LinearBuckets.Adjacency.Represents G rows)
    (fuel level : ℕ) (r : Fin n) (base marks : Vector (Option ℕ) n) (frontier : List (Fin n))
    (hi : LayerInvariant G r base level marks frontier) (v : Fin n) :
    v∈(explore rows fuel level frontier marks).members ↔
      G.Reachable r v ∧ level≤G.dist r v ∧ G.dist r v<level+fuel := by
  induction fuel generalizing level marks frontier with
  | zero => simp [explore] <;> omega
  | succ fuel ih =>
    cases frontier with
    | nil =>
      simp only [explore,List.not_mem_nil,false_iff,not_and]
      intro hv
      have h := hi.no_later rows hr v hv
      omega
    | cons w ws =>
      change v∈(w::ws)++(explore rows fuel (level+1) (expand rows level (w::ws) marks).next
        (expand rows level (w::ws) marks).marks).members ↔ _
      rw [List.mem_append,hi.frontier_eq,
        ih (level+1) (expand rows level (w::ws) marks).marks (expand rows level (w::ws) marks).next (hi.expand rows hr)]
      constructor
      · rintro (⟨hR,hd⟩ | ⟨hR,hl,hu⟩) <;> exact ⟨hR,by omega,by omega⟩
      · rintro ⟨hR,hl,hu⟩
        by_cases he : G.dist r v=level
        · exact Or.inl ⟨hR,he⟩
        · exact Or.inr ⟨hR,by omega,by omega⟩

lemma explore_members_nodup {n : ℕ} {G : SimpleGraph (Fin n)}
    (rows : Vector (List (Fin n)) n) (hr : LinearBuckets.Adjacency.Represents G rows)
    (fuel level : ℕ) (r : Fin n) (base marks : Vector (Option ℕ) n) (frontier : List (Fin n))
    (hi : LayerInvariant G r base level marks frontier) :
    (explore rows fuel level frontier marks).members.Nodup := by
  induction fuel generalizing level marks frontier with
  | zero => simp [explore]
  | succ fuel ih =>
    cases frontier with
    | nil => simp [explore]
    | cons w ws =>
      have ht := ih (level+1) (expand rows level (w::ws) marks).marks (expand rows level (w::ws) marks).next (hi.expand rows hr)
      apply List.nodup_append.mpr
      refine ⟨hi.nodup,ht,?_⟩
      intro a ha b hb hab
      subst b
      have h1 := (hi.frontier_eq a).mp ha
      have h2 := (explore_members rows hr fuel (level+1) r base (expand rows level (w::ws) marks).marks
        (expand rows level (w::ws) marks).next (hi.expand rows hr) a).mp hb
      omega

lemma initial_invariant {n : ℕ} {G : SimpleGraph (Fin n)} (r : Fin n) (base : Vector (Option ℕ) n)
    (hb : ∀v, G.Reachable r v → base[v.val]=none) :
    LayerInvariant G r base 0 (base.set r.val (some 0)) [r] := by
  refine ⟨hb,?_,?_,by simp⟩
  · intro v
    by_cases hv : v=r
    · subst v;simp
    · have he : r.val≠v.val := fun h => hv (Fin.ext h.symm)
      by_cases hR : G.Reachable r v
      · have hd : G.dist r v≠0 := fun h => hv (hR.dist_eq_zero_iff.mp h).symm
        simp [he,hR,hd]
      · simp [he,hR]
  · intro v
    simp only [List.mem_singleton]
    constructor
    · rintro rfl;exact ⟨Reachable.refl _,by simp⟩
    · rintro ⟨hR,hd⟩;exact (hR.dist_eq_zero_iff.mp hd).symm

lemma reachable_dist_lt {n : ℕ} {G : SimpleGraph (Fin n)} (r v : Fin n) (hr : G.Reachable r v) :
    G.dist r v<n := by
  obtain ⟨p,hp,he⟩ := hr.exists_path_of_dist
  have h := hp.length_lt
  simpa only [Fintype.card_fin,he] using h

/-- A single shared-mark component extraction gives exactly its true graph
component, preserving all previous marks and computing ordinary shortest distances. -/
theorem start_spec {n : ℕ} {G : SimpleGraph (Fin n)}
    (rows : Vector (List (Fin n)) n) (hr : LinearBuckets.Adjacency.Represents G rows)
    (r : Fin n) (base : Vector (Option ℕ) n) (hb : ∀v, G.Reachable r v → base[v.val]=none) :
    (∀v, (start rows r base).marks[v.val] = if G.Reachable r v then some (G.dist r v) else base[v.val]) ∧
    (∀v, v∈(start rows r base).members ↔ G.Reachable r v) ∧
    (start rows r base).members.Nodup ∧ (start rows r base).frontier=[] := by
  have hi := initial_invariant r base hb
  have ho := explore_invariant rows hr n 0 r base (base.set r.val (some 0)) [r] hi
  refine ⟨?_,?_,explore_members_nodup rows hr n 0 r base _ _ hi,?_⟩
  · intro v
    change (explore rows n 0 [r] (base.set r.val (some 0))).marks[v.val]=_
    rw [ho.marks_eq]
    by_cases hR : G.Reachable r v
    · have hd := reachable_dist_lt r v hR
      simp [hR,hd.le]
    · simp [hR]
  · intro v
    have hm := explore_members rows hr n 0 r base (base.set r.val (some 0)) [r] hi v
    change v∈(explore rows n 0 [r] (base.set r.val (some 0))).members ↔ _
    rw [hm]
    constructor
    · exact fun h => h.1
    · intro hR;exact ⟨hR,Nat.zero_le _,by simpa using reachable_dist_lt r v hR⟩
  · apply List.eq_nil_iff_forall_not_mem.mpr
    intro v hv
    obtain ⟨hR,hd⟩ := (ho.frontier_eq v).mp hv
    have hlt := reachable_dist_lt r v hR
    omega

end HiddenCircuits.DH.ComponentForest
