import HiddenCircuits.DH.LexBFSModel

/-! Correctness of stable ordered-partition LexBFS, independently of the pointer implementation. -/
namespace HiddenCircuits.DH.LexBFSModel

@[simp] lemma nonemptyCell_flatten {V : Type*} (xs : List V) :
    (nonemptyCell xs).flatten = xs := by
  by_cases hx : xs = [] <;> simp [nonemptyCell,hx]

lemma mem_nonemptyCell {V : Type*} {xs ys : List V} :
    ys ∈ nonemptyCell xs ↔ ys = xs ∧ xs ≠ [] := by
  by_cases hx : xs = [] <;> simp [nonemptyCell,hx]

lemma splitCell_perm {V : Type*} (first : Bool) (a : V → Bool) (xs : List V) :
    (splitCell first a xs).flatten.Perm xs := by
  cases first
  · simpa [splitCell] using (List.perm_append_comm :
      (xs.filter (fun x => !a x) ++ xs.filter a).Perm _).trans (List.filter_append_perm a xs)
  · simpa [splitCell] using List.filter_append_perm a xs

lemma refine_perm {V : Type*} (first : Bool) (a : V → Bool) (p : Partition V) :
    (LexBFSModel.refine first a p).flatten.Perm p.flatten := by
  induction p with
  | nil => exact .nil
  | cons cell p ih =>
    simpa [refine,List.flatMap_cons,List.flatten_append] using
      (splitCell_perm first a cell).append ih

lemma pop_perm {V : Type*} {p q : Partition V} {v : V} {size : ℕ}
    (h : pop p = some (v,size,q)) : (v::q.flatten).Perm p.flatten := by
  induction p with
  | nil => simp [LexBFSModel.pop] at h
  | cons cell p ih =>
    cases cell with
    | nil => simpa using ih h
    | cons w ws =>
      simp only [LexBFSModel.pop,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl,rfl⟩ := h
      simp

lemma pop_none {V : Type*} (p : Partition V) : pop p = none ↔ p.flatten = [] := by
  induction p with
  | nil => simp [LexBFSModel.pop]
  | cons cell p ih => cases cell <;> simp [LexBFSModel.pop,ih]

lemma pop_some_of_nonempty {V : Type*} {p : Partition V} (hp : p.flatten ≠ []) :
    ∃ v size q, pop p = some (v,size,q) := by
  cases h : pop p with
  | none => exact False.elim (hp ((pop_none p).mp h))
  | some e => exact ⟨e.1,e.2.1,e.2.2,rfl⟩

lemma run_perm {V : Type*} (a : V → V → Bool) (first : Bool)
    (fuel : ℕ) (p : Partition V) (hf : p.flatten.length ≤ fuel) :
    ((run a first fuel p).map Event.vertex).Perm p.flatten := by
  induction fuel generalizing p with
  | zero =>
    have hp : p.flatten = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hf)
    simp [run,hp]
  | succ fuel ih =>
    cases h : pop p with
    | none => simp [run,h,(pop_none p).mp h]
    | some e =>
      rcases e with ⟨v,size,q⟩
      have hp := pop_perm h
      have hr := refine_perm first (a v) q
      have hlen : (LexBFSModel.refine first (a v) q).flatten.length ≤ fuel := by
        have hl := hp.length_eq
        have hrlen := hr.length_eq
        rw [List.length_cons] at hl
        omega
      have ht := ih (LexBFSModel.refine first (a v) q) hlen
      simpa [run,h] using ((ht.trans hr).cons v).trans hp

/-- Ordinary and complement sweeps visit every input vertex exactly once. -/
theorem sweep_perm {V : Type*} (a : V → V → Bool) (first : Bool) (tieOrder : List V) :
    ((sweep a first tieOrder).map Event.vertex).Perm tieOrder := by
  simpa [sweep] using run_perm a first tieOrder.length (nonemptyCell tieOrder) (by simp)

/-- Equal adjacency profiles to all already-selected pivots. -/
def SameProfile {V : Type*} (prefer : V → V → Bool) (past : List V) (u v : V) : Prop :=
  ∀ x ∈ past, prefer x u = prefer x v

/-- The first different earlier pivot prefers `u`. This is strict lexicographic priority. -/
def Ahead {V : Type*} (prefer : V → V → Bool) (past : List V) (u v : V) : Prop :=
  ∃ before x after, past = before ++ x::after ∧ SameProfile prefer before u v ∧
    prefer x u = true ∧ prefer x v = false

lemma SameProfile.refl {V : Type*} (prefer : V → V → Bool) (past : List V) (u : V) :
    SameProfile prefer past u u := fun _ _ => rfl

lemma SameProfile.symm {V : Type*} {prefer : V → V → Bool} {past : List V} {u v : V}
    (h : SameProfile prefer past u v) : SameProfile prefer past v u := fun x hx => (h x hx).symm

lemma SameProfile.append {V : Type*} {prefer : V → V → Bool} {past : List V} {u v x : V}
    (h : SameProfile prefer past u v) (hx : prefer x u = prefer x v) :
    SameProfile prefer (past ++ [x]) u v := by
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · exact h y hy
  · simpa using (List.mem_singleton.mp hy ▸ hx)

lemma Ahead.append {V : Type*} {prefer : V → V → Bool} {past : List V} {u v : V}
    (h : Ahead prefer past u v) (later : List V) : Ahead prefer (past ++ later) u v := by
  obtain ⟨before,x,after,hp,hs,hu,hv⟩ := h
  exact ⟨before,x,after++later,by simp [hp,List.append_assoc],hs,hu,hv⟩

lemma Ahead.not_same {V : Type*} {prefer : V → V → Bool} {past : List V} {u v : V}
    (h : Ahead prefer past u v) : ¬SameProfile prefer past u v := by
  obtain ⟨before,x,after,hp,_,hu,hv⟩ := h
  intro he
  have hx := he x (by simp [hp])
  simp [hu,hv] at hx

/-- Cells are homogeneous and ordered strictly by their adjacency profiles. -/
def Profiles {V : Type*} (prefer : V → V → Bool) (past : List V) (p : Partition V) : Prop :=
  (∀ cell ∈ p, ∀ u ∈ cell, ∀ v ∈ cell, SameProfile prefer past u v) ∧
    p.Pairwise (fun c d => ∀ u ∈ c, ∀ v ∈ d, Ahead prefer past u v)

lemma Profiles.initial {V : Type*} (prefer : V → V → Bool) (tie : List V) :
    Profiles prefer [] (nonemptyCell tie) := by
  by_cases ht : tie = []
  · simp [Profiles,nonemptyCell,ht]
  · simp only [Profiles,nonemptyCell,ht,↓reduceIte,List.mem_singleton,List.pairwise_singleton,and_true]
    intro cell hcell u hu v hv
    simp [SameProfile]

lemma splitCell_as_preferred {V : Type*} (first : Bool) (a : V → Bool) (xs : List V) :
    splitCell first a xs = splitCell true (fun x => a x == first) xs := by
  cases first <;> simp [splitCell]

lemma splitCell_sublist {V : Type*} {a : V → Bool} {xs ys : List V}
    (h : ys ∈ splitCell true a xs) : ys.Sublist xs := by
  simp only [splitCell,↓reduceIte,List.mem_append,mem_nonemptyCell] at h
  rcases h with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> exact List.filter_sublist

lemma pairwise_nonemptyCell {V : Type*} (R : List V → List V → Prop) (xs : List V) :
    (nonemptyCell xs).Pairwise R := by
  by_cases hx : xs = [] <;> simp [nonemptyCell,hx]

lemma profiles_splitCell {V : Type*} {prefer : V → V → Bool} {past xs : List V} (pivot : V)
    (hs : ∀ u ∈ xs, ∀ v ∈ xs, SameProfile prefer past u v) :
    Profiles prefer (past++[pivot]) (splitCell true (prefer pivot) xs) := by
  constructor
  · intro cell hc u hu v hv
    simp only [splitCell,↓reduceIte,List.mem_append,mem_nonemptyCell] at hc
    rcases hc with ⟨rfl,_⟩ | ⟨rfl,_⟩
    · have huf := List.mem_filter.mp hu
      have hvf := List.mem_filter.mp hv
      exact (hs u huf.1 v hvf.1).append (huf.2.trans hvf.2.symm)
    · have huf := List.mem_filter.mp hu
      have hvf := List.mem_filter.mp hv
      have he : prefer pivot u = prefer pivot v := by
        have hu0 : prefer pivot u = false := by simpa using huf.2
        have hv0 : prefer pivot v = false := by simpa using hvf.2
        exact hu0.trans hv0.symm
      exact (hs u huf.1 v hvf.1).append he
  · simp only [splitCell,↓reduceIte]
    refine List.pairwise_append.mpr ⟨pairwise_nonemptyCell _ _,pairwise_nonemptyCell _ _,?_⟩
    intro c hc d hd u hu v hv
    obtain ⟨rfl,_⟩ := mem_nonemptyCell.mp hc
    obtain ⟨rfl,_⟩ := mem_nonemptyCell.mp hd
    have huf := List.mem_filter.mp hu
    have hvf := List.mem_filter.mp hv
    exact ⟨past,pivot,[],by simp,hs u huf.1 v hvf.1,huf.2,by simpa using hvf.2⟩

/-- A pivot refinement appends exactly its adjacency bit to each remaining profile. -/
lemma Profiles.refine {V : Type*} {prefer : V → V → Bool} {past : List V} {p : Partition V}
    (h : Profiles prefer past p) (pivot : V) :
    Profiles prefer (past++[pivot]) (LexBFSModel.refine true (prefer pivot) p) := by
  constructor
  · intro cell hc u hu v hv
    obtain ⟨old,ho,hc⟩ := List.mem_flatMap.mp hc
    exact (profiles_splitCell pivot (h.1 old ho)).1 cell hc u hu v hv
  · apply List.pairwise_flatMap.mpr
    constructor
    · intro cell hc
      exact (profiles_splitCell pivot (h.1 cell hc)).2
    · apply h.2.imp
      intro old old' hold c hc d hd u hu v hv
      exact (hold u ((splitCell_sublist hc).subset hu)
        v ((splitCell_sublist hd).subset hv)).append [pivot]

lemma Profiles.tail {V : Type*} {prefer : V → V → Bool} {past cell : List V} {p : Partition V}
    (h : Profiles prefer past (cell::p)) : Profiles prefer past p :=
  ⟨fun c hc => h.1 c (List.mem_cons_of_mem _ hc),h.2.tail⟩

lemma Profiles.replace_head {V : Type*} {prefer : V → V → Bool} {past cell small : List V}
    {p : Partition V} (h : Profiles prefer past (cell::p)) (hs : small.Sublist cell) :
    Profiles prefer past (nonemptyCell small ++ p) := by
  by_cases hz : small = []
  · simpa [nonemptyCell,hz] using h.tail
  · simp only [nonemptyCell,hz,↓reduceIte,List.singleton_append]
    constructor
    · intro c hc u hu v hv
      rcases List.mem_cons.mp hc with rfl | hc
      · exact h.1 cell List.mem_cons_self u (hs.subset hu) v (hs.subset hv)
      · exact h.1 c (List.mem_cons_of_mem _ hc) u hu v hv
    · refine List.pairwise_cons.mpr ⟨?_,h.2.tail⟩
      intro c hc u hu v hv
      exact (List.pairwise_cons.mp h.2).1 c hc u (hs.subset hu) v hv

lemma Profiles.pop {V : Type*} {prefer : V → V → Bool} {past : List V} {p q : Partition V}
    {pivot : V} {size : ℕ} (h : Profiles prefer past p) (hp : LexBFSModel.pop p = some (pivot,size,q)) :
    Profiles prefer past q ∧
      ∀ v ∈ q.flatten, SameProfile prefer past pivot v ∨ Ahead prefer past pivot v := by
  induction p with
  | nil => simp [LexBFSModel.pop] at hp
  | cons cell p ih =>
    cases cell with
    | nil => exact ih h.tail hp
    | cons u us =>
      simp only [LexBFSModel.pop,Option.some.injEq,Prod.mk.injEq] at hp
      obtain ⟨rfl,rfl,rfl⟩ := hp
      refine ⟨h.replace_head (List.sublist_cons_self _ _),?_⟩
      intro v hv
      simp only [List.flatten_append,nonemptyCell_flatten,List.mem_append] at hv
      rcases hv with hv | hv
      · exact Or.inl (h.1 (u::us) List.mem_cons_self u List.mem_cons_self v
          (List.mem_cons_of_mem _ hv))
      · obtain ⟨c,hc,hv⟩ := List.mem_flatten.mp hv
        exact Or.inr ((List.pairwise_cons.mp h.2).1 c hc u List.mem_cons_self v hv)

lemma Profiles.step {V : Type*} (a : V → V → Bool) (first : Bool)
    {past : List V} {p q : Partition V} {pivot : V} {size : ℕ}
    (h : Profiles (prefers a first) past p) (hp : LexBFSModel.pop p = some (pivot,size,q)) :
    Profiles (prefers a first) (past++[pivot]) (LexBFSModel.refine first (a pivot) q) := by
  have hr := (h.pop hp).1.refine pivot
  have he : LexBFSModel.refine first (a pivot) q = LexBFSModel.refine true (prefers a first pivot) q := by
    unfold LexBFSModel.refine
    apply congrArg (fun f => q.flatMap f)
    funext cell
    exact splitCell_as_preferred first (a pivot) cell
  rw [he]
  exact hr

/-- At each selection, its past profile weakly dominates every later selected vertex. -/
def ValidOrder {V : Type*} (prefer : V → V → Bool) : List V → List V → Prop
  | _,[] => True
  | past,v::later => (∀ z ∈ later, SameProfile prefer past v z ∨ Ahead prefer past v z) ∧
      ValidOrder prefer (past++[v]) later

lemma run_order {V : Type*} (a : V → V → Bool) (first : Bool) (fuel : ℕ)
    (past : List V) (p : Partition V) (hf : p.flatten.length ≤ fuel)
    (hp : Profiles (prefers a first) past p) :
    ValidOrder (prefers a first) past ((run a first fuel p).map Event.vertex) := by
  induction fuel generalizing past p with
  | zero => trivial
  | succ fuel ih =>
    cases h : pop p with
    | none => simp [run,h,ValidOrder]
    | some e =>
      rcases e with ⟨v,size,q⟩
      have hpop := pop_perm h
      have hr := refine_perm first (a v) q
      have hlen : (refine first (a v) q).flatten.length ≤ fuel := by
        have h1 := hpop.length_eq
        have h2 := hr.length_eq
        simp only [List.length_cons] at h1
        omega
      have ht := run_perm a first fuel (refine first (a v) q) hlen
      simp only [run,h,List.map_cons,ValidOrder]
      refine ⟨?_,ih (past++[v]) _ hlen (hp.step a first h)⟩
      intro z hz
      exact (hp.pop h).2 z ((ht.trans hr).mem_iff.mp hz)

/-- Both sweep modes satisfy the ordinary first-differing-pivot definition of LexBFS. -/
theorem sweep_order {V : Type*} (a : V → V → Bool) (first : Bool) (tie : List V) :
    ValidOrder (prefers a first) [] ((sweep a first tie).map Event.vertex) := by
  exact run_order a first tie.length [] (nonemptyCell tie) (by simp) (Profiles.initial _ _)

lemma ValidOrder.drop_prefix {V : Type*} {prefer : V → V → Bool} {past before later : List V}
    (h : ValidOrder prefer past (before++later)) : ValidOrder prefer (past++before) later := by
  induction before generalizing past with
  | nil => simpa using h
  | cons v before ih =>
    have ht := ih h.2
    simpa [List.append_assoc] using ht

/-- A contradictory adjacency bit at `x` forces the first favorable bit to occur strictly earlier. -/
lemma Ahead.witness_before {V : Type*} {prefer : V → V → Bool} (before : List V)
    {x y z : V} {between : List V} (h : Ahead prefer (before++x::between) y z)
    (hy : prefer x y = false) (hz : prefer x z = true) :
    ∃ w ∈ before, prefer w y = true ∧ prefer w z = false := by
  induction before with
  | nil =>
    obtain ⟨front,w,back,he,hs,hwy,hwz⟩ := h
    cases front with
    | nil =>
      have hx : x=w := (List.cons.inj he).1
      subst w
      simp [hy] at hwy
    | cons v vs =>
      have hx : x=v := (List.cons.inj he).1
      have heq := hs v List.mem_cons_self
      rw [← hx,hy,hz] at heq
      contradiction
  | cons b before ih =>
    obtain ⟨front,w,back,he,hs,hwy,hwz⟩ := h
    cases front with
    | nil =>
      have hb : b=w := (List.cons.inj he).1
      exact ⟨w,by simp [hb],hwy,hwz⟩
    | cons v vs =>
      have ht : before++x::between = vs++w::back := (List.cons.inj he).2
      have ha : Ahead prefer (before++x::between) y z :=
        ⟨vs,w,back,ht,fun u hu => hs u (List.mem_cons_of_mem _ hu),hwy,hwz⟩
      obtain ⟨u,hu,huy,huz⟩ := ih ha
      exact ⟨u,List.mem_cons_of_mem _ hu,huy,huz⟩

/-- The standard LexBFS four-point condition, phrased with concrete list positions. -/
def FourPoint {V : Type*} (prefer : V → V → Bool) (order : List V) : Prop :=
  ∀ before x middle y between z after,
    order = before++x::middle++y::between++z::after →
    prefer x z = true → prefer x y = false →
    ∃ w ∈ before, prefer w y = true ∧ prefer w z = false

lemma ValidOrder.fourPoint {V : Type*} {prefer : V → V → Bool} {order : List V}
    (h : ValidOrder prefer [] order) : FourPoint prefer order := by
  intro before x middle y between z after he hxz hxy
  subst order
  have hsplit : ValidOrder prefer [] ((before++x::middle)++(y::between++z::after)) := by
    simpa [List.append_assoc] using h
  have hy := hsplit.drop_prefix
  simp only [List.nil_append] at hy
  have hp := hy.1 z (by simp)
  rcases hp with hp | hp
  · have heq := hp x (by simp)
    simp [hxy,hxz] at heq
  · exact hp.witness_before before hxy hxz

theorem sweep_fourPoint {V : Type*} (a : V → V → Bool) (first : Bool) (tie : List V) :
    FourPoint (prefers a first) ((sweep a first tie).map Event.vertex) :=
  (sweep_order a first tie).fourPoint

lemma refine_append {V : Type*} (first : Bool) (a : V → Bool) (p q : Partition V) :
    refine first a (p++q) = refine first a p ++ refine first a q := by simp [refine]

lemma pop_append {V : Type*} {p q : Partition V} {v : V} {size : ℕ}
    (hp : pop p = some (v,size,q)) (tail : Partition V) :
    pop (p++tail) = some (v,size,q++tail) := by
  induction p with
  | nil => simp [pop] at hp
  | cons cell p ih =>
    cases cell with
    | nil => exact ih hp
    | cons u us =>
      simp only [pop,Option.some.injEq,Prod.mk.injEq] at hp
      obtain ⟨rfl,rfl,rfl⟩ := hp
      simp [pop,List.append_assoc]

/-- Refinement never interleaves pre-existing cells: all vertices in a prefix of cells
are visited before any vertex in the remaining cells. -/
lemma run_prefix_perm {V : Type*} (a : V → V → Bool) (first : Bool) (fuel : ℕ)
    (left right : Partition V) (hf : (left++right).flatten.length ≤ fuel) :
    (((run a first fuel (left++right)).map Event.vertex).take left.flatten.length).Perm left.flatten := by
  induction fuel generalizing left right with
  | zero =>
    have hz : left.flatten = [] := by
      have hl : left.flatten.length = 0 := by simp only [List.flatten_append,List.length_append] at hf; omega
      exact List.length_eq_zero_iff.mp hl
    simp [run,hz]
  | succ fuel ih =>
    by_cases hz : left.flatten = []
    · simp [hz]
    obtain ⟨v,size,q,hpop⟩ := pop_some_of_nonempty hz
    have hfull := pop_append hpop right
    have hlperm := pop_perm hpop
    have hrperm := refine_perm first (a v) q
    have htotal := pop_perm hfull
    have hrall := refine_perm first (a v) (q++right)
    have hlen : (refine first (a v) q ++ refine first (a v) right).flatten.length ≤ fuel := by
      have h1 := htotal.length_eq
      have h2 := hrall.length_eq
      rw [refine_append] at h2
      simp only [List.length_cons] at h1
      omega
    have hcount : left.flatten.length = (refine first (a v) q).flatten.length+1 := by
      have h1 := hlperm.length_eq
      have h2 := hrperm.length_eq
      simp only [List.length_cons] at h1
      omega
    rw [show (run a first (fuel+1) (left++right)).map Event.vertex =
        v::(run a first fuel (refine first (a v) q ++ refine first (a v) right)).map Event.vertex by
      simp [run,hfull,refine_append],hcount,List.take_succ_cons]
    exact ((ih _ _ hlen).cons v).trans ((hrperm.cons v).trans hlperm)

/-- Canonical partitions contain no empty cells; this is maintained by either sweep. -/
def Canonical {V : Type*} (p : Partition V) : Prop := ∀ c ∈ p, c ≠ []

lemma nonemptyCell_canonical {V : Type*} (xs : List V) : Canonical (nonemptyCell xs) := by
  intro c hc
  obtain ⟨rfl,hne⟩ := mem_nonemptyCell.mp hc
  exact hne

lemma refine_canonical {V : Type*} (first : Bool) (a : V → Bool) (p : Partition V) :
    Canonical (refine first a p) := by
  intro c hc
  obtain ⟨old,_,hc⟩ := List.mem_flatMap.mp hc
  rw [splitCell_as_preferred] at hc
  simp only [splitCell,↓reduceIte,List.mem_append] at hc
  rcases hc with hc | hc <;> exact nonemptyCell_canonical _ c hc

lemma Profiles.first_cell {V : Type*} {prefer : V → V → Bool} {past cell : List V}
    {p : Partition V} {pivot v : V} (h : Profiles prefer past (cell::p)) (hp : pivot ∈ cell) :
    (v ∈ (cell::p).flatten ∧ SameProfile prefer past pivot v) ↔ v ∈ cell := by
  constructor
  · rintro ⟨hv,hs⟩
    rcases List.mem_append.mp hv with hv | hv
    · exact hv
    · obtain ⟨d,hd,hv⟩ := List.mem_flatten.mp hv
      exact False.elim (((List.pairwise_cons.mp h.2).1 d hd pivot hp v hv).not_same hs)
  · intro hv
    exact ⟨by simp [hv],h.1 cell List.mem_cons_self pivot hp v hv⟩

/-- Each compact slice length identifies exactly the current equal-profile class.
The recursive past is specification-only; it is not a runtime snapshot array. -/
def SliceCorrect {V : Type*} (prefer : V → V → Bool) : List V → List (Event V) → Prop
  | _,[] => True
  | past,e::es => 0 < e.sliceSize ∧ e.sliceSize ≤ (e::es).length ∧
      (∀ v, v ∈ ((e::es).map Event.vertex).take e.sliceSize ↔
        v ∈ (e::es).map Event.vertex ∧ SameProfile prefer past e.vertex v) ∧
      SliceCorrect prefer (past++[e.vertex]) es

lemma run_slices {V : Type*} (a : V → V → Bool) (first : Bool) (fuel : ℕ)
    (past : List V) (p : Partition V) (hf : p.flatten.length ≤ fuel)
    (hc : Canonical p) (hp : Profiles (prefers a first) past p) :
    SliceCorrect (prefers a first) past (run a first fuel p) := by
  induction fuel generalizing past p with
  | zero => trivial
  | succ fuel ih =>
    cases p with
    | nil => trivial
    | cons cell p =>
      cases cell with
      | nil => exact False.elim (hc [] List.mem_cons_self rfl)
      | cons v vs =>
        let q := nonemptyCell vs ++ p
        let next := refine first (a v) q
        have hpop : pop ((v::vs)::p) = some (v,vs.length+1,q) := rfl
        have hper := pop_perm hpop
        have hr := refine_perm first (a v) q
        have hlen : next.flatten.length ≤ fuel := by
          have h1 := hper.length_eq
          have h2 := hr.length_eq
          simp only [List.length_cons] at h1
          change next.flatten.length = q.flatten.length at h2
          omega
        have htail := ih (past++[v]) next hlen (refine_canonical _ _ _) (hp.step a first hpop)
        have ht := run_perm a first (fuel+1) ((v::vs)::p) hf
        have hprefix := run_prefix_perm a first (fuel+1) [v::vs] p hf
        change SliceCorrect (prefers a first) past
          (⟨v,vs.length+1⟩::run a first fuel next)
        refine ⟨Nat.zero_lt_succ _,?_,?_,htail⟩
        · have hlength := ht.length_eq
          simp only [run,hpop,List.length_map,List.length_cons,List.length_flatten,List.map_cons,List.sum_cons] at hlength
          change (vs.length+1) ≤ (⟨v,vs.length+1⟩::run a first fuel next).length
          change (run a first fuel next).length+1 = (vs.length+1)+(p.map List.length).sum at hlength
          simp only [List.length_cons]
          omega
        · intro u
          have hpre : u ∈ ((⟨v,vs.length+1⟩::run a first fuel next).map Event.vertex).take (vs.length+1) ↔
              u ∈ v::vs := by
            simpa only [List.singleton_append,List.flatten_cons,List.flatten_nil,List.append_nil,
              run,hpop,List.length_cons] using hprefix.mem_iff (a := u)
          rw [hpre]
          symm
          have hmem : u ∈ (⟨v,vs.length+1⟩::run a first fuel next).map Event.vertex ↔
              u ∈ ((v::vs)::p).flatten := by simpa only [run,hpop] using ht.mem_iff (a := u)
          rw [hmem]
          exact hp.first_cell List.mem_cons_self

theorem sweep_slices {V : Type*} (a : V → V → Bool) (first : Bool) (tie : List V) :
    SliceCorrect (prefers a first) [] (sweep a first tie) :=
  run_slices a first tie.length [] (nonemptyCell tie) (by simp)
    (nonemptyCell_canonical tie) (Profiles.initial _ _)

/-- Every cell retains the supplied strict tie ranking. -/
def StableTie {V : Type*} (rank : V → ℕ) (p : Partition V) : Prop :=
  ∀ cell ∈ p, cell.Pairwise (fun u v => rank u < rank v)

lemma StableTie.initial {V : Type*} {rank : V → ℕ} {tie : List V}
    (h : tie.Pairwise (fun u v => rank u < rank v)) : StableTie rank (nonemptyCell tie) := by
  intro cell hc
  obtain ⟨rfl,_⟩ := mem_nonemptyCell.mp hc
  exact h

lemma StableTie.refine {V : Type*} {rank : V → ℕ} {p : Partition V}
    (h : StableTie rank p) (first : Bool) (a : V → Bool) :
    StableTie rank (LexBFSModel.refine first a p) := by
  intro cell hc
  obtain ⟨old,ho,hc⟩ := List.mem_flatMap.mp hc
  rw [splitCell_as_preferred] at hc
  exact (h old ho).sublist (splitCell_sublist hc)

lemma StableTie.pop {V : Type*} {rank : V → ℕ} {p q : Partition V} {v : V} {size : ℕ}
    (h : StableTie rank p) (hp : LexBFSModel.pop p = some (v,size,q)) : StableTie rank q := by
  induction p with
  | nil => simp [LexBFSModel.pop] at hp
  | cons cell p ih =>
    cases cell with
    | nil => exact ih (fun c hc => h c (List.mem_cons_of_mem _ hc)) hp
    | cons u us =>
      simp only [LexBFSModel.pop,Option.some.injEq,Prod.mk.injEq] at hp
      obtain ⟨rfl,rfl,rfl⟩ := hp
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · rw [(mem_nonemptyCell.mp hc).1]
        exact (h (u::us) List.mem_cons_self).tail
      · exact h c (List.mem_cons_of_mem _ hc)

/-- The pivot is the least tie-ranked vertex of its exact slice. -/
def TieCorrect {V : Type*} (rank : V → ℕ) (prefer : V → V → Bool) :
    List V → List (Event V) → Prop
  | _,[] => True
  | past,e::es => (∀ v ∈ (e::es).map Event.vertex,
      SameProfile prefer past e.vertex v → rank e.vertex ≤ rank v) ∧
      TieCorrect rank prefer (past++[e.vertex]) es

lemma run_ties {V : Type*} (a : V → V → Bool) (first : Bool) (rank : V → ℕ)
    (fuel : ℕ) (past : List V) (p : Partition V) (hf : p.flatten.length ≤ fuel)
    (hc : Canonical p) (hp : Profiles (prefers a first) past p) (htie : StableTie rank p) :
    TieCorrect rank (prefers a first) past (run a first fuel p) := by
  induction fuel generalizing past p with
  | zero => trivial
  | succ fuel ih =>
    cases p with
    | nil => trivial
    | cons cell p =>
      cases cell with
      | nil => exact False.elim (hc [] List.mem_cons_self rfl)
      | cons v vs =>
        let q := nonemptyCell vs ++ p
        let next := refine first (a v) q
        have hpop : pop ((v::vs)::p) = some (v,vs.length+1,q) := rfl
        have hper := pop_perm hpop
        have hr := refine_perm first (a v) q
        have hlen : next.flatten.length ≤ fuel := by
          have h1 := hper.length_eq
          have h2 := hr.length_eq
          simp only [List.length_cons] at h1
          change next.flatten.length = q.flatten.length at h2
          omega
        have htail := ih (past++[v]) next hlen (refine_canonical _ _ _) (hp.step a first hpop)
          ((htie.pop hpop).refine first (a v))
        have ht := run_perm a first (fuel+1) ((v::vs)::p) hf
        change TieCorrect rank (prefers a first) past (⟨v,vs.length+1⟩::run a first fuel next)
        refine ⟨?_,htail⟩
        intro u hu hsame
        have hm : u ∈ ((v::vs)::p).flatten := ht.mem_iff.mp hu
        have hcell := hp.first_cell List.mem_cons_self |>.mp ⟨hm,hsame⟩
        rcases List.mem_cons.mp hcell with rfl | hu
        · exact le_rfl
        · exact Nat.le_of_lt ((List.pairwise_cons.mp (htie (v::vs) List.mem_cons_self)).1 u hu)

theorem sweep_ties {V : Type*} (a : V → V → Bool) (first : Bool) (rank : V → ℕ)
    (tie : List V) (ht : tie.Pairwise (fun u v => rank u < rank v)) :
    TieCorrect rank (prefers a first) [] (sweep a first tie) :=
  run_ties a first rank tie.length [] (nonemptyCell tie) (by simp)
    (nonemptyCell_canonical tie) (Profiles.initial _ _) (StableTie.initial ht)

lemma SliceCorrect.drop_prefix {V : Type*} {prefer : V → V → Bool} {past : List V}
    {before later : List (Event V)} (h : SliceCorrect prefer past (before++later)) :
    SliceCorrect prefer (past++before.map Event.vertex) later := by
  induction before generalizing past with
  | nil => simpa using h
  | cons e before ih =>
    have ht := ih h.2.2.2
    simpa [List.append_assoc] using ht

lemma TieCorrect.drop_prefix {V : Type*} {rank : V → ℕ} {prefer : V → V → Bool} {past : List V}
    {before later : List (Event V)} (h : TieCorrect rank prefer past (before++later)) :
    TieCorrect rank prefer (past++before.map Event.vertex) later := by
  induction before generalizing past with
  | nil => simpa using h
  | cons e before ih =>
    have ht := ih h.2
    simpa [List.append_assoc] using ht

/-- No nonneighbor of the first pivot can precede one of its preferred neighbors. -/
lemma FourPoint.first_preferred {V : Type*} {prefer : V → V → Bool} {order : List V}
    (h : FourPoint prefer order) {root y z : V} {before between after : List V}
    (he : order = root::before++y::between++z::after) (hz : prefer root z = true) :
    prefer root y = true := by
  by_cases hy : prefer root y = true
  · exact hy
  · have hy' : prefer root y = false := by simpa using hy
    obtain ⟨w,hw,_⟩ := h [] root before y between z after (by simpa using he) hz hy'
    simp at hw

private lemma pairwise_of_split {V : Type*} {R : V → V → Prop} (xs : List V)
    (h : ∀ before y between z after, xs = before++y::between++z::after → R y z) :
    xs.Pairwise R := by
  induction xs with
  | nil => simp
  | cons v vs ih =>
    refine List.pairwise_cons.mpr ⟨?_,ih ?_⟩
    · intro z hz
      obtain ⟨between,after,he⟩ := List.mem_iff_append.mp hz
      exact h [] v between z after (by simp [he])
    · intro before y between z after he
      exact h (v::before) y between z after (by simp [he])

/-- All first-pivot neighbors form a contiguous initial block of the remaining sweep. -/
lemma FourPoint.first_block {V : Type*} {prefer : V → V → Bool} {root : V} {rest : List V}
    (h : FourPoint prefer (root::rest)) :
    rest.Pairwise (fun y z => prefer root z = true → prefer root y = true) := by
  apply pairwise_of_split
  intro before y between z after he hz
  exact h.first_preferred (before := before) (between := between) (after := after) (by simp [he]) hz

/-- Before the first visit to a uniform group, tie breaking selects its least-ranked vertex. -/
lemma TieCorrect.first_group_min {V : Type*} {rank : V → ℕ} {prefer : V → V → Bool}
    {before after : List (Event V)} {e : Event V} {M : Set V}
    (h : TieCorrect rank prefer [] (before++e::after)) (he : e.vertex ∈ M)
    (hbefore : ∀ b ∈ before, b.vertex ∉ M)
    (hcovered : ∀ v ∈ M, v ∈ (before++e::after).map Event.vertex)
    (hprofile : ∀ x ∈ before.map Event.vertex, ∀ u ∈ M, ∀ v ∈ M, prefer x u = prefer x v) :
    ∀ v ∈ M, rank e.vertex ≤ rank v := by
  intro v hv
  have ht := h.drop_prefix
  simp only [List.nil_append] at ht
  have hm := hcovered v hv
  simp only [List.map_append,List.mem_append] at hm
  have hremain : v ∈ (e::after).map Event.vertex := by
    rcases hm with hm | hm
    · obtain ⟨b,hb,hbv⟩ := List.mem_map.mp hm
      exact False.elim (hbefore b hb (hbv ▸ hv))
    · exact hm
  exact ht.1 v hremain (fun x hx => hprofile x hx e.vertex he v hv)

lemma TieCorrect.first_group_eq {V : Type*} {rank : V → ℕ} {prefer : V → V → Bool}
    {before after : List (Event V)} {e : Event V} {M : Set V} {first : V}
    (h : TieCorrect rank prefer [] (before++e::after)) (he : e.vertex ∈ M)
    (hbefore : ∀ b ∈ before, b.vertex ∉ M)
    (hcovered : ∀ v ∈ M, v ∈ (before++e::after).map Event.vertex)
    (hprofile : ∀ x ∈ before.map Event.vertex, ∀ u ∈ M, ∀ v ∈ M, prefer x u = prefer x v)
    (hf : first ∈ M) (hmin : ∀ v ∈ M, rank first ≤ rank v) (hinj : Function.Injective rank) :
    e.vertex = first :=
  hinj (Nat.le_antisymm (h.first_group_min he hbefore hcovered hprofile first hf) (hmin e.vertex he))

/-- Transport a compact event through a vertex relabeling, retaining its slice size. -/
def Event.map {V W : Type*} (f : V → W) (e : Event V) : Event W := ⟨f e.vertex,e.sliceSize⟩

lemma nonemptyCell_map {V W : Type*} (f : V → W) (xs : List V) :
    nonemptyCell (xs.map f) = (nonemptyCell xs).map (List.map f) := by
  cases xs <;> simp [nonemptyCell]

lemma splitCell_map {V W : Type*} (f : V → W) (first : Bool) (a : W → Bool) (xs : List V) :
    splitCell first a (xs.map f) =
      (splitCell first (fun v => a (f v)) xs).map (List.map f) := by
  cases first <;> simp [splitCell,List.filter_map,nonemptyCell_map,Function.comp_def]

lemma refine_map {V W : Type*} (f : V → W) (first : Bool) (a : W → Bool) (p : Partition V) :
    refine first a (p.map (List.map f)) =
      (refine first (fun v => a (f v)) p).map (List.map f) := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    simp only [List.map_cons,refine,List.flatMap_cons,splitCell_map,List.map_append]
    exact congrArg (fun rest => (splitCell first (fun v => a (f v)) c).map (List.map f) ++ rest) ih

lemma pop_map {V W : Type*} (f : V → W) (p : Partition V) :
    pop (p.map (List.map f)) = (pop p).map (fun q => (f q.1,q.2.1,q.2.2.map (List.map f))) := by
  induction p with
  | nil => rfl
  | cons c p ih => cases c <;> simp [pop,ih,nonemptyCell_map]

/-- Relabeling the graph and the input tie order commutes with every concrete sweep step. -/
lemma run_map {V W : Type*} (f : V → W) (a : W → W → Bool) (first : Bool)
    (fuel : ℕ) (p : Partition V) :
    run a first fuel (p.map (List.map f)) =
      (run (fun u v => a (f u) (f v)) first fuel p).map (Event.map f) := by
  induction fuel generalizing p with
  | zero => rfl
  | succ fuel ih =>
    simp only [run,pop_map]
    cases hp : pop p with
    | none => rfl
    | some e =>
      rcases e with ⟨v,size,q⟩
      simp only [Option.map_some,List.map_cons,Event.map]
      rw [refine_map,ih]

lemma sweep_map {V W : Type*} (f : V → W) (a : W → W → Bool) (first : Bool) (tie : List V) :
    sweep a first (tie.map f) =
      (sweep (fun u v => a (f u) (f v)) first tie).map (Event.map f) := by
  simp only [sweep,List.length_map,nonemptyCell_map,run_map]

lemma splitCell_congr_on {V : Type*} (first : Bool) (a b : V → Bool) (cell : List V)
    (h : ∀ v ∈ cell, a v=b v) : splitCell first a cell = splitCell first b cell := by
  have hy : cell.filter a = cell.filter b := List.filter_congr h
  have hn : cell.filter (fun v => !a v) = cell.filter (fun v => !b v) :=
    List.filter_congr (fun v hv => congrArg Bool.not (h v hv))
  cases first <;> simp [splitCell,hy,hn]

lemma refine_congr_on {V : Type*} (first : Bool) (a b : V → Bool) (p : Partition V)
    (h : ∀ v ∈ p.flatten, a v=b v) : refine first a p = refine first b p := by
  induction p with
  | nil => rfl
  | cons cell p ih =>
    simp only [refine,List.flatMap_cons]
    rw [splitCell_congr_on first a b cell (fun v hv => h v (List.mem_append_left _ hv))]
    exact congrArg (List.append _) (ih (fun v hv => h v (List.mem_append_right _ hv)))

lemma refine_complement {V : Type*} (a : V → Bool) (p : Partition V) :
    refine false a p = refine true (fun v => !a v) p := by
  unfold refine
  congr 1
  funext cell
  simpa using splitCell_as_preferred false a cell

/-- Diagonal bits are never read by refinement, since the pivot has already been removed. -/
lemma run_complement_offdiag {V : Type*} (a b : V → V → Bool)
    (hab : ∀ u v, u≠v → b u v = !a u v) (fuel : ℕ) (p : Partition V) (hn : p.flatten.Nodup) :
    run a false fuel p = run b true fuel p := by
  induction fuel generalizing p with
  | zero => rfl
  | succ fuel ih =>
    cases hp : pop p with
    | none => simp [run,hp]
    | some e =>
      rcases e with ⟨v,size,q⟩
      have hn' := (pop_perm hp).nodup_iff.mpr hn
      obtain ⟨hv,hnq⟩ := List.nodup_cons.mp hn'
      have he : refine false (a v) q = refine true (b v) q := by
        rw [refine_complement]
        apply refine_congr_on
        intro u hu
        exact (hab v u (fun he => hv (he ▸ hu))).symm
      have hnext : (refine true (b v) q).flatten.Nodup :=
        (refine_perm true (b v) q).nodup_iff.mpr hnq
      simp only [run,hp,he]
      exact congrArg (List.cons ⟨v,size⟩) (ih _ hnext)

/-- The complement flag is literally a normal sweep of the graph complement, on every
ordinary duplicate-free vertex order, without constructing complement adjacency rows. -/
theorem sweep_graph_complement {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (tie : List V) (hn : tie.Nodup) :
    sweep (fun u v => decide (G.Adj u v)) false tie =
      sweep (fun u v => decide (Gᶜ.Adj u v)) true tie := by
  apply run_complement_offdiag
  · intro u v huv
    simp [G.compl_adj,huv]
  · simpa using hn

end HiddenCircuits.DH.LexBFSModel
