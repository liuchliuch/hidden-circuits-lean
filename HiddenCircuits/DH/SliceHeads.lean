import HiddenCircuits.DH.LexBFSSemantics

/-! A single stack pass recovers immediate slice parents from compact LexBFS
slice lengths. Stack pushes and pops are explicitly counted and amortized. -/
namespace HiddenCircuits.DH.SliceHeads
open LexBFSModel
variable {V : Type*}

structure Frame (V : Type*) where
  vertex : V
  start : ℕ
  stop : ℕ
  deriving Repr, DecidableEq

structure ParentEvent (V : Type*) where
  frame : Frame V
  parent : Option (Frame V)
  deriving Repr, DecidableEq

/-- Expired intervals form a stack prefix on properly nested input. -/
def trim (i : ℕ) : List (Frame V) → List (Frame V) × ℕ
  | [] => ([],1)
  | f::fs => if f.stop ≤ i then
      let q := trim i fs
      (q.1,q.2+2)
    else (f::fs,1)

/-- Endpoints increase going down the stack. -/
def NestedStack (stack : List (Frame V)) : Prop :=
  stack.Pairwise (fun f g => f.stop ≤ g.stop)

lemma trim_sublist (i : ℕ) (stack : List (Frame V)) : (trim i stack).1.Sublist stack := by
  induction stack with
  | nil => simp [trim]
  | cons f fs ih =>
    by_cases h : f.stop ≤ i
    · simpa [trim,h] using ih.cons f
    · simp [trim,h]

lemma trim_nested (i : ℕ) {stack : List (Frame V)} (hs : NestedStack stack) :
    NestedStack (trim i stack).1 := hs.sublist (trim_sublist i stack)

lemma trim_values (i : ℕ) {stack : List (Frame V)} (hs : NestedStack stack) :
    (trim i stack).1 = stack.filter (fun f => i < f.stop) := by
  induction stack with
  | nil => simp [trim]
  | cons f fs ih =>
    have ht := (List.pairwise_cons.mp hs).2
    by_cases hf : f.stop ≤ i
    · simp [trim,hf,show ¬i<f.stop by omega,ih ht]
    · have hall : ∀g∈fs, i<g.stop := by
        intro g hg
        have := (List.pairwise_cons.mp hs).1 g hg
        omega
      have he : fs.filter (fun g => i < g.stop) = fs :=
        List.filter_eq_self.mpr (by intro g hg; simpa using hall g hg)
      simp [trim,hf,show i<f.stop by omega,he]

/-- Each popped frame releases two units of potential; the final test costs one. -/
lemma trim_amortized (i : ℕ) (stack : List (Frame V)) :
    (trim i stack).2 + 2*(trim i stack).1.length = 2*stack.length+1 := by
  induction stack with
  | nil => simp [trim]
  | cons f fs ih =>
    by_cases hf : f.stop ≤ i <;> simp [trim,hf] <;> omega

structure Result (V : Type*) where
  events : List (ParentEvent V)
  stack : List (Frame V)
  accesses : ℕ
  deriving Repr

/-- The actual pass uses only the event list and an endpoint stack. It neither
copies complete slices nor scans an alphabet or vertex array at each node. -/
def scan (i : ℕ) (events : List (Event V)) (stack : List (Frame V)) : Result V :=
  match events with
  | [] => ⟨[],stack,0⟩
  | e::es =>
      let t := trim i stack
      let f := Frame.mk e.vertex i (i+e.sliceSize)
      let q := scan (i+1) es (f::t.1)
      ⟨⟨f,t.1.head?⟩::q.events,q.stack,q.accesses+t.2+6⟩

def build (events : List (Event V)) : Result V := scan 0 events []

@[simp] lemma scan_length (i : ℕ) (events : List (Event V)) (stack : List (Frame V)) :
    (scan i events stack).events.length = events.length := by
  induction events generalizing i stack <;> simp [scan, *]

lemma scan_vertices (i : ℕ) (events : List (Event V)) (stack : List (Frame V)) :
    (scan i events stack).events.map (fun p => p.frame.vertex) = events.map Event.vertex := by
  induction events generalizing i stack <;> simp [scan, *]

/-- The stack-potential argument charges every push and pop once. -/
theorem scan_amortized (i : ℕ) (events : List (Event V)) (stack : List (Frame V)) :
    (scan i events stack).accesses + 2*(scan i events stack).stack.length =
      9*events.length+2*stack.length := by
  induction events generalizing i stack with
  | nil => simp [scan]
  | cons e es ih =>
    have h := ih (i+1) (⟨e.vertex,i,i+e.sliceSize⟩::(trim i stack).1)
    have ht := trim_amortized i stack
    simp only [scan,List.length_cons] at *
    omega

/-- Immediate-parent recovery is linear in the number of compact events. -/
theorem build_accesses (events : List (Event V)) : (build events).accesses ≤ 9*events.length := by
  have h := scan_amortized 0 events []
  simp only [List.length_nil,mul_zero,add_zero] at h
  exact Nat.le.intro h

/-- Literal interval nesting, with no stack or execution predicate in the input. -/
def Laminar (frames : List (Frame V)) : Prop :=
  frames.Pairwise (fun f g => f.start < g.start ∧ (g.start < f.stop → g.stop ≤ f.stop))

/-- A frame is an active predecessor at a given sweep position. -/
def Active (i : ℕ) (f : Frame V) : Prop := f.start < i ∧ i < f.stop

/-- The parent is the latest active earlier interval. -/
def IsParent (past : List (Frame V)) (f : Frame V) (p : Option (Frame V)) : Prop :=
  p = ((past.reverse).filter (fun a => f.start < a.stop)).head?

/-- Converting compact lengths into the actual integer intervals is itself a
single traversal, used here only to state the parser's input/output semantics. -/
def framesFrom (i : ℕ) : List (Event V) → List (Frame V)
  | [] => []
  | e::es => ⟨e.vertex,i,i+e.sliceSize⟩::framesFrom (i+1) es

lemma scan_frames (i : ℕ) (events : List (Event V)) (stack : List (Frame V)) :
    (scan i events stack).events.map ParentEvent.frame = framesFrom i events := by
  induction events generalizing i stack <;> simp [scan,framesFrom, *]

/-- Filtering a prefix of chronological intervals leaves endpoints nested in
reverse order, when every overlap is containment. -/
lemma laminar_active_nested {past : List (Frame V)} (hl : Laminar past) (i : ℕ)
    (hbefore : ∀f∈past, f.start < i) :
    NestedStack (past.reverse.filter (fun f => i < f.stop)) := by
  rw [List.filter_reverse]
  apply List.Pairwise.reverse
  apply (hl.filter _).imp_of_mem
  intro f g hf hg h
  have hfa : i < f.stop := by simpa using (List.mem_filter.mp hf).2
  have hga : g.start < i := hbefore g (List.mem_filter.mp hg).1
  exact h.2 (by omega)

lemma filter_stop_mono (i j : ℕ) (hij : i≤j) (xs : List (Frame V)) :
    (xs.filter (fun f => i<f.stop)).filter (fun f => j<f.stop) =
      xs.filter (fun f => j<f.stop) := by
  induction xs with
  | nil => simp
  | cons f fs ih =>
    by_cases hj : j<f.stop
    · have hi : i<f.stop := by omega
      simp [hj,hi,ih]
    · by_cases hi : i<f.stop <;> simp [hj,hi,ih]

/-- The output parent at each position is the latest active containing interval
among all earlier input events. -/
def ParentCorrect (past : List (Frame V)) : List (ParentEvent V) → Prop
  | [] => True
  | e::es => IsParent past e.frame e.parent ∧ ParentCorrect (past++[e.frame]) es

lemma scan_parent_correct (i : ℕ) (events : List (Event V))
    (past stack : List (Frame V))
    (hl : Laminar (past++framesFrom i events)) (hs : NestedStack stack)
    (ha : (trim i stack).1 = past.reverse.filter (fun f => i<f.stop)) :
    ParentCorrect past (scan i events stack).events := by
  induction events generalizing i past stack with
  | nil => trivial
  | cons e es ih =>
    let f : Frame V := ⟨e.vertex,i,i+e.sliceSize⟩
    have hs' : NestedStack (f::(trim i stack).1) := by
      refine List.pairwise_cons.mpr ⟨?_,trim_nested i hs⟩
      intro g hg
      rw [ha] at hg
      obtain ⟨hgp,hgi⟩ := List.mem_filter.mp hg
      have hgp' : g∈past := List.mem_reverse.mp hgp
      have hgi' : i<g.stop := by simpa using hgi
      have hrel := (List.pairwise_append.mp hl).2.2 g hgp' f (by simp [framesFrom,f])
      exact hrel.2 hgi'
    have hl' : Laminar ((past++[f])++framesFrom (i+1) es) := by
      simpa only [framesFrom,List.append_assoc,List.singleton_append] using hl
    have ha' : (trim (i+1) (f::(trim i stack).1)).1 =
        (past++[f]).reverse.filter (fun g => i+1<g.stop) := by
      rw [trim_values (i+1) hs',ha]
      simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,
        List.singleton_append,List.filter_cons]
      rw [filter_stop_mono i (i+1) (by omega)]
    have htail := ih (i+1) (past++[f]) (f::(trim i stack).1) hl' hs' ha'
    change IsParent past f (trim i stack).1.head? ∧ _
    exact ⟨by simp only [IsParent,f,ha],htail⟩

/-- On literal laminar intervals the one-pass parser reports exactly the parent
of every compact slice. No parent forest is supplied as an algorithm input. -/
theorem build_parent_correct (events : List (Event V))
    (hl : Laminar (framesFrom 0 events)) : ParentCorrect [] (build events).events := by
  exact scan_parent_correct 0 events [] [] (by simpa using hl) (by simp [NestedStack]) rfl

lemma framesFrom_start_le (i : ℕ) (events : List (Event V)) {f : Frame V}
    (hf : f∈framesFrom i events) : i≤f.start := by
  induction events generalizing i with
  | nil => simp [framesFrom] at hf
  | cons e es ih =>
    rcases List.mem_cons.mp hf with rfl | hf
    · exact le_rfl
    · have := ih (i+1) hf; omega

lemma pop_size_le {p q : Partition V} {v : V} {size : ℕ}
    (h : pop p = some (v,size,q)) : size≤p.flatten.length := by
  induction p with
  | nil => simp [pop] at h
  | cons cell p ih =>
    cases cell with
    | nil => simpa using ih h
    | cons u us =>
      simp only [pop,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl,rfl⟩ := h
      simp

/-- Refinement never lets an event's slice extend beyond its current prefix of
partition cells. This is a structural property of the actual sweep evaluator. -/
lemma run_prefix_bounded (a : V → V → Bool) (s : Bool) (fuel i : ℕ)
    (left right : Partition V) :
    ∀f∈framesFrom i (run a s fuel (left++right)),
      f.start < i + left.flatten.length → f.stop ≤ i + left.flatten.length := by
  induction fuel generalizing i left right with
  | zero => simp [run,framesFrom]
  | succ fuel ih =>
    by_cases hz : left.flatten = []
    · intro f hf hbefore
      have hlo := framesFrom_start_le i _ hf
      simp only [hz,List.length_nil,add_zero] at hbefore
      omega
    · obtain ⟨v,size,q,hpop⟩ := pop_some_of_nonempty hz
      have hfull := pop_append hpop right
      have hsize := pop_size_le hpop
      have hlen := (pop_perm hpop).length_eq
      have href := (refine_perm s (a v) q).length_eq
      have hcount : (refine s (a v) q).flatten.length+1=left.flatten.length := by
        simp only [List.length_cons] at hlen
        omega
      intro f hf hbefore
      simp only [run,hfull,refine_append,framesFrom,List.mem_cons] at hf
      rcases hf with rfl | hf
      · change i + size ≤ i + left.flatten.length
        omega
      · have hb : f.start < (i+1)+(refine s (a v) q).flatten.length := by omega
        have hh := ih (i+1) (refine s (a v) q) (refine s (a v) right) f hf hb
        omega

/-- Every compact sweep, on either graph or complement, has literal nested or
disjoint slice intervals. No semantic graph hypothesis is necessary. -/
theorem run_laminar (a : V → V → Bool) (s : Bool) (fuel i : ℕ)
    (p : Partition V) (hc : Canonical p) : Laminar (framesFrom i (run a s fuel p)) := by
  induction fuel generalizing i p with
  | zero => simp [run,framesFrom,Laminar]
  | succ fuel ih =>
    cases p with
    | nil => simp [run,pop,framesFrom,Laminar]
    | cons cell p =>
      cases cell with
      | nil => exact False.elim (hc [] List.mem_cons_self rfl)
      | cons v vs =>
        let left := refine s (a v) (nonemptyCell vs)
        let right := refine s (a v) p
        have hrun : run a s (fuel+1) ((v::vs)::p) =
            ⟨v,vs.length+1⟩::run a s fuel (left++right) := by
          simp [run,pop,left,right,refine_append]
        rw [hrun,framesFrom]
        refine List.pairwise_cons.mpr ⟨?_,ih (i+1) (left++right) ?_⟩
        · intro f hf
          have hstart := framesFrom_start_le (i+1) _ hf
          refine ⟨by change i<f.start; omega,?_⟩
          have hlen : left.flatten.length=vs.length := by
            simpa only [left,nonemptyCell_flatten] using (refine_perm s (a v) (nonemptyCell vs)).length_eq
          intro hbefore
          have hb : f.start < (i+1)+left.flatten.length := by
            change f.start < i+(vs.length+1) at hbefore
            omega
          have hh := run_prefix_bounded a s fuel (i+1) left right f hf hb
          change f.stop ≤ i+(vs.length+1)
          omega
        · simpa only [left,right,← refine_append] using
            refine_canonical s (a v) (nonemptyCell vs++p)

theorem sweep_laminar (a : V → V → Bool) (s : Bool) (tie : List V) :
    Laminar (framesFrom 0 (sweep a s tie)) :=
  run_laminar a s tie.length 0 (nonemptyCell tie) (nonemptyCell_canonical tie)

/-- Ordinary sweep input produces the exact immediate-slice parents and costs at
most nine stack/list operations per vertex event. -/
theorem build_sweep_spec (a : V → V → Bool) (s : Bool) (tie : List V) :
    ParentCorrect [] (build (sweep a s tie)).events ∧
      (build (sweep a s tie)).accesses≤9*tie.length := by
  refine ⟨build_parent_correct _ (sweep_laminar a s tie),?_⟩
  have he := (sweep_perm a s tie).length_eq
  simp only [List.length_map] at he
  simpa only [he] using build_accesses (sweep a s tie)

lemma ParentCorrect.at_split {past : List (Frame V)} {before after : List (ParentEvent V)}
    {p : ParentEvent V} (h : ParentCorrect past (before++p::after)) :
    IsParent (past++before.map ParentEvent.frame) p.frame p.parent := by
  induction before generalizing past with
  | nil => simpa using h.1
  | cons e before ih =>
    have ht := ih h.2
    simpa [List.append_assoc] using ht

lemma head_some_mem {α : Type*} {xs : List α} {x : α} (h : xs.head?=some x) : x∈xs := by
  cases xs with
  | nil => simp at h
  | cons a as => simp only [List.head?_cons,Option.some.injEq] at h; simp [h]

/-- Latest active predecessor, stated as a parent interval followed by no active
intermediate interval. This is the exact test used by the stack machine. -/
lemma latest_filter_eq {α : Type*} (p : α → Bool) (before middle : List α) (x : α)
    (hx : x∉middle) :
    (((before++x::middle).reverse).filter p).head?=some x ↔
      p x=true ∧ ∀y∈middle, p y=false := by
  constructor
  · intro h
    have hxP := (List.mem_filter.mp (head_some_mem h)).2
    have hsplit : (((middle.reverse).filter p) ++ (x::before.reverse).filter p).head?=some x := by
      have hrev : (before++x::middle).reverse = middle.reverse++x::before.reverse := by
        simp [List.append_assoc]
      simpa only [hrev,List.filter_append] using h
    have hnil : middle.reverse.filter p=[] := by
      cases hm : middle.reverse.filter p with
      | nil => rfl
      | cons y ys =>
        have hyx : y=x := by simpa only [hm,List.cons_append,List.head?_cons,Option.some.injEq] using hsplit
        subst y
        have hmem : x∈middle.reverse.filter p := by rw [hm]; simp
        exact False.elim (hx (List.mem_reverse.mp (List.mem_filter.mp hmem).1))
    refine ⟨hxP,?_⟩
    intro y hy
    by_contra hn
    have hp : p y=true := by simpa using hn
    have hmem : y∈middle.reverse.filter p := List.mem_filter.mpr ⟨List.mem_reverse.mpr hy,hp⟩
    simpa only [hnil,List.not_mem_nil] using hmem
  · rintro ⟨hp,hm⟩
    have hnil : middle.reverse.filter p=[] := List.filter_eq_nil_iff.mpr (by
      intro y hy; simp [hm y (List.mem_reverse.mp hy)])
    simp [List.reverse_append,List.reverse_cons,List.filter_append,hnil,hp]

lemma IsParent.eq_some_iff {before middle : List (Frame V)} {p f : Frame V}
    (hp : p∉middle) :
    IsParent (before++p::middle) f (some p) ↔
      f.start < p.stop ∧ ∀g∈middle, g.stop≤f.start := by
  unfold IsParent
  rw [eq_comm,latest_filter_eq _ before middle p hp]
  simp

lemma framesFrom_append (i : ℕ) (before after : List (Event V)) :
    framesFrom i (before++after) = framesFrom i before ++ framesFrom (i+before.length) after := by
  induction before generalizing i with
  | nil => simp [framesFrom]
  | cons e es ih => simp [framesFrom,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

lemma mem_framesFrom (i : ℕ) (events : List (Event V)) (f : Frame V) :
    f∈framesFrom i events ↔ ∃before e after, events=before++e::after ∧
      f=⟨e.vertex,i+before.length,i+before.length+e.sliceSize⟩ := by
  constructor
  · induction events generalizing i with
    | nil => simp [framesFrom]
    | cons e es ih =>
      intro h
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨[],e,es,rfl,by simp⟩
      · obtain ⟨before,g,after,he,hf⟩ := ih (i+1) h
        exact ⟨e::before,g,after,by simp [he],by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hf⟩
  · rintro ⟨before,e,after,rfl,rfl⟩
    rw [framesFrom_append]
    exact List.mem_append_right _ (by simp [framesFrom])

end HiddenCircuits.DH.SliceHeads
