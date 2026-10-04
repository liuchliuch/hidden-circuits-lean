import HiddenCircuits.DH.Cographs

/-! Finite graph-level assembly for semantic distance-hereditary preprocessing. -/
namespace HiddenCircuits.DH
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

/-- The original vertices in a component of an induced graph. -/
def componentVertices (S : Set V) (C : (G.induce S).ConnectedComponent) : Set V :=
  Subtype.val '' C.supp

lemma componentVertices_subset (S : Set V) (C : (G.induce S).ConnectedComponent) :
    componentVertices S C ⊆ S := by
  rintro x ⟨y,hy,rfl⟩
  exact y.property

lemma componentVertices_connected (S : Set V) (C : (G.induce S).ConnectedComponent) :
    (G.induce (componentVertices S C)).Connected := by
  let e := inducedImageIso (G := G) S C.supp
  exact C.connected_toSimpleGraph.map e.toHom e.toEquiv.surjective

lemma componentVertices_closed (S : Set V) (C : (G.induce S).ConnectedComponent)
    {u x : V} (hu : u ∈ componentVertices S C) (hx : x ∈ S) (hux : G.Adj u x) :
    x ∈ componentVertices S C := by
  obtain ⟨u',hu',he⟩ := hu
  refine ⟨⟨x,hx⟩,C.mem_supp_of_adj_mem_supp hu' ?_,rfl⟩
  change G.Adj u'.val x
  simpa [he] using hux

/-- Actual connected components of a farthest layer are modules of the input graph. -/
theorem DistanceHereditaryGraph.farthest_component_module
    (hG : DistanceHereditaryGraph G) (hc : G.Connected) (r : V) (k : ℕ)
    (hmax : ∀ x, G.dist r x ≤ k)
    (C : (G.induce {x | G.dist r x = k}).ConnectedComponent) :
    GraphModule G (componentVertices {x | G.dist r x = k} C) := by
  apply hG.farthest_layer_module hc r k hmax
  · exact fun x hx => componentVertices_subset _ C hx
  · exact (componentVertices_connected _ C).preconnected
  · exact fun u hu x ha hx => componentVertices_closed _ C hu hx ha

/-- The predecessor module has no induced four-vertex path. -/
theorem DistanceHereditaryGraph.predecessors_p4Free
    (hG : DistanceHereditaryGraph G) (r u : V) : P4Free (G.induce (predecessors G r u)) := by
  let f : G.induce (predecessors G r u) ↪g G.induce (G.neighborSet u) := {
    toFun x := ⟨x.val,x.property.1.symm⟩
    inj' := by
      intro x y h
      exact Subtype.ext (congrArg (fun z : G.neighborSet u => z.val) h)
    map_rel_iff' := by intro x y; rfl }
  exact (hG.neighborhood_p4Free u).of_embedding f

/-- A finite nonempty layer has a vertex whose predecessor set is inclusion-minimal. -/
lemma exists_minimal_predecessors [Finite V] (r u : V) :
    ∃ v, G.dist r v = G.dist r u ∧
      ∀ z, G.dist r z = G.dist r v →
        predecessors G r z ⊆ predecessors G r v →
        predecessors G r v ⊆ predecessors G r z := by
  classical
  letI := Fintype.ofFinite V
  let L := Finset.univ.filter (fun v => G.dist r v = G.dist r u)
  have hL : L.Nonempty := ⟨u,by simp [L]⟩
  obtain ⟨v,hv,hmin⟩ := L.exists_min_image (fun v => (predecessors G r v).ncard) hL
  have hvlevel : G.dist r v = G.dist r u := (Finset.mem_filter.mp hv).2
  refine ⟨v,hvlevel,?_⟩
  intro z hz hsub
  have hzL : z ∈ L := by simp [L,hz,hvlevel]
  have hcard := hmin z hzL
  have heq : predecessors G r z = predecessors G r v :=
    Set.eq_of_subset_of_ncard_le hsub hcard
  exact heq ▸ Set.Subset.rfl

/-- Finite assembly of the BFS pruning argument. The sole independent input is
the cograph theorem for ordinary induced subgraphs; no pruning sequence is assumed. -/
theorem DistanceHereditaryGraph.exists_reduction_of_p4free_twins
    [Finite V] [Nontrivial V] (hG : DistanceHereditaryGraph G) (hc : G.Connected)
    (hTw : ∀ S : Set V, S.Nontrivial → P4Free (G.induce S) →
      ∃ u v : S, TwinPair (G.induce S) u v) :
    ∃ u v : V, PendantPair G u v ∨ TwinPair G u v := by
  classical
  letI := Fintype.ofFinite V
  let r : V := Classical.choice hc.nonempty
  obtain ⟨f,hf,hfmax⟩ := Finset.univ.exists_max_image (fun v => G.dist r v) Finset.univ_nonempty
  let k := G.dist r f
  have hmax (x : V) : G.dist r x ≤ k := hfmax x (Finset.mem_univ x)
  have hpos : 0 < k := by
    obtain ⟨x,hxr⟩ := exists_ne r
    have hdist := hc.pos_dist_of_ne hxr.symm
    have := hmax x
    omega
  by_cases hedge : ∃ a b : V, G.dist r a = k ∧ G.dist r b = k ∧ G.Adj a b
  · obtain ⟨a,b,ha,hb,hab⟩ := hedge
    let L : Set V := {x | G.dist r x = k}
    let a' : L := ⟨a,ha⟩
    let b' : L := ⟨b,hb⟩
    let C := (G.induce L).connectedComponentMk a'
    let S := componentVertices L C
    have haC : a' ∈ C.supp := by simp [C,ConnectedComponent.mem_supp_iff]
    have hbC : b' ∈ C.supp := C.mem_supp_of_adj_mem_supp haC hab
    have haS : a ∈ S := ⟨a',haC,rfl⟩
    have hbS : b ∈ S := ⟨b',hbC,rfl⟩
    have hS : S.Nontrivial := ⟨a,haS,b,hbS,hab.ne⟩
    have hfree : P4Free (G.induce S) := (hG.layer_p4Free hc r k).of_embedding
      (G.induceHomOfLE (componentVertices_subset L C))
    have hmodule : GraphModule G S := hG.farthest_component_module hc r k hmax C
    obtain ⟨u,v,ht⟩ := hTw S hS hfree
    exact ⟨u.val,v.val,Or.inr (ht.of_induce_module hmodule)⟩
  · obtain ⟨u,hu,hmin⟩ := exists_minimal_predecessors (G := G) r f
    have hulevel : G.dist r u = k := hu
    let S := predecessors G r u
    have hSne : S.Nonempty := predecessors_nonempty (hc r u) (by omega)
    by_cases hSn : S.Nontrivial
    · have hmodule : GraphModule G S := hG.minimal_predecessors_module hc r u hmin
      obtain ⟨v,w,ht⟩ := hTw S hSn (hG.predecessors_p4Free r u)
      exact ⟨v.val,w.val,Or.inr (ht.of_induce_module hmodule)⟩
    · have hSs : S.Subsingleton := Set.not_nontrivial_iff.mp hSn
      obtain ⟨v,hv⟩ := hSne
      refine ⟨v,u,Or.inl ⟨hv.1.symm,?_⟩⟩
      intro x hux
      have hx : x ∈ S := by
        refine ⟨hux.symm,?_⟩
        have hdiff := hux.diff_dist_adj (u := r)
        have hbound := hmax x
        have hxne : G.dist r x ≠ k := fun he => hedge ⟨u,x,hulevel,he,hux⟩
        omega
      exact hSs hx hv

/-- Every nontrivial finite connected distance-hereditary graph has an actual
pendant vertex or an actual twin pair. Distance heredity is the semantic metric
predicate, and no reduction certificate is supplied. -/
theorem DistanceHereditaryGraph.exists_pendant_or_twins
    [Finite V] [Nontrivial V] (hG : DistanceHereditaryGraph G) (hc : G.Connected) :
    ∃ u v : V, PendantPair G u v ∨ TwinPair G u v := by
  apply hG.exists_reduction_of_p4free_twins hc
  intro S hS hfree
  letI : Nontrivial S := by
    obtain ⟨a,ha,b,hb,hab⟩ := hS
    exact ⟨⟨⟨a,ha⟩,⟨b,hb⟩,fun he => hab (congrArg Subtype.val he)⟩⟩
  exact hfree.exists_twins

namespace LaminarMarking

/-- Result of an actual mark-array pass; `accesses` counts array reads, writes,
equality tests and Boolean conjunctions explicitly executed by these loops. -/
structure Result (n : ℕ) where
  accepted : Bool
  marks : Vector Nat n
  accesses : ℕ

/-- Scan every incidence in a neighborhood and compare its mark to the anchor. -/
def checkMarks {n : ℕ} (marks : Vector Nat n) (tag : ℕ) : List (Fin n) → Bool × ℕ
  | [] => (true,0)
  | x :: xs =>
      let q := checkMarks marks tag xs
      ((marks[x.val] == tag) && q.1,q.2+3)

/-- Set exactly the listed positions to the new neighborhood's tag. -/
def writeMarks {n : ℕ} (tag : ℕ) : List (Fin n) → Vector Nat n → Vector Nat n × ℕ
  | [],marks => (marks,0)
  | x :: xs,marks =>
      let q := writeMarks tag xs (marks.set x.val tag)
      (q.1,q.2+1)

/-- Uehara--Uno's marking pass, after neighborhoods have been size-ordered.
No graph-class certificate or laminarity proof is an input to this program. -/
def scan {n : ℕ} (tag : ℕ) (rows : List (List (Fin n))) (marks : Vector Nat n) : Result n :=
  match rows with
  | [] => ⟨true,marks,0⟩
  | [] :: rows =>
      let q := scan (tag+1) rows marks
      ⟨q.accepted,q.marks,q.accesses+2⟩
  | (x :: xs) :: rows =>
      let c := checkMarks marks marks[x.val] (x :: xs)
      if c.1 then
        let w := writeMarks tag (x :: xs) marks
        let q := scan (tag+1) rows w.1
        ⟨q.accepted,q.marks,q.accesses+c.2+w.2+3⟩
      else ⟨false,marks,c.2+2⟩

/-- Total size of the actual neighborhood incidence lists. -/
def incidenceCount {n : ℕ} (rows : List (List (Fin n))) : ℕ :=
  (rows.map List.length).sum

@[simp] lemma checkMarks_accesses {n : ℕ} (marks : Vector Nat n) (tag : ℕ)
    (xs : List (Fin n)) : (checkMarks marks tag xs).2 = 3*xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [checkMarks,ih]; omega

@[simp] lemma writeMarks_accesses {n : ℕ} (marks : Vector Nat n) (tag : ℕ)
    (xs : List (Fin n)) : (writeMarks tag xs marks).2 = xs.length := by
  induction xs generalizing marks with
  | nil => rfl
  | cons x xs ih => simp [writeMarks,ih]

@[simp] lemma checkMarks_true {n : ℕ} (marks : Vector Nat n) (tag : ℕ)
    (xs : List (Fin n)) : (checkMarks marks tag xs).1 = true ↔
      ∀ x ∈ xs, marks[x.val] = tag := by
  induction xs with
  | nil => simp [checkMarks]
  | cons x xs ih => simp [checkMarks,ih]

lemma writeMarks_get {n : ℕ} (marks : Vector Nat n) (tag : ℕ)
    (xs : List (Fin n)) (y : Fin n) :
    (writeMarks tag xs marks).1[y.val] = if y ∈ xs then tag else marks[y.val] := by
  induction xs generalizing marks with
  | nil => simp [writeMarks]
  | cons x xs ih =>
    simp only [writeMarks,ih,List.mem_cons]
    by_cases hy : y ∈ xs
    · simp [hy]
    · by_cases he : y = x
      · subst x; simp [hy]
      · have hev : x.val ≠ y.val := fun h => he (Fin.ext h.symm)
        simp [hy,he,hev]

/-- The actual marking loops use a linear number of explicit array/Boolean
operations, on every input, including inputs rejected as non-laminar. -/
theorem scan_accesses_le {n : ℕ} (tag : ℕ) (rows : List (List (Fin n)))
    (marks : Vector Nat n) :
    (scan tag rows marks).accesses ≤ 4*incidenceCount rows+3*rows.length := by
  induction rows generalizing tag marks with
  | nil => simp [scan,incidenceCount]
  | cons row rows ih =>
    cases row with
    | nil =>
      have h := ih (tag+1) marks
      simp only [scan,incidenceCount,List.map_cons,List.length_nil,List.sum_cons,
        zero_add,List.length_cons] at *
      omega
    | cons x xs =>
      have h := ih (tag+1) (writeMarks tag (x :: xs) marks).1
      simp only [scan]
      split
      · simp only [checkMarks_accesses,writeMarks_accesses,List.length_cons]
        simp only [incidenceCount,List.map_cons,List.sum_cons,List.length_cons] at *
        omega
      · simp only [checkMarks_accesses,List.length_cons]
        simp only [incidenceCount,List.map_cons,List.sum_cons,List.length_cons]
        omega

/-- All incidences of a row currently carry one mark. -/
def Uniform {n : ℕ} (marks : Vector Nat n) (row : List (Fin n)) : Prop :=
  ∀ x ∈ row, ∀ y ∈ row, marks[x.val] = marks[y.val]

/-- In processing order, a later set is contained in or disjoint from each
earlier set. Duplicate neighborhoods are allowed. -/
def DescendingLaminar {n : ℕ} (rows : List (List (Fin n))) : Prop :=
  rows.Pairwise (fun a b => (∀ x ∈ b, x ∈ a) ∨ (∀ x ∈ b, x ∉ a))

lemma writeMarks_preserves_uniform {n : ℕ} (marks : Vector Nat n) (tag : ℕ)
    (a b : List (Fin n)) (hb : Uniform marks b)
    (hrel : (∀ x ∈ b, x ∈ a) ∨ (∀ x ∈ b, x ∉ a)) :
    Uniform (writeMarks tag a marks).1 b := by
  intro x hx y hy
  rw [writeMarks_get,writeMarks_get]
  rcases hrel with h | h
  · simp [h x hx,h y hy]
  · simpa [h x hx,h y hy] using hb x hx y hy

/-- The implementation accepts every descending laminar family. The proof
tracks the actual mark vector, rather than assuming a successful trace. -/
theorem scan_accepts_of_descending {n : ℕ} (tag : ℕ)
    (rows : List (List (Fin n))) (marks : Vector Nat n)
    (hrows : DescendingLaminar rows) (hu : ∀ row ∈ rows, Uniform marks row) :
    (scan tag rows marks).accepted = true := by
  induction rows generalizing tag marks with
  | nil => rfl
  | cons row rows ih =>
    obtain ⟨hrel,htail⟩ := List.pairwise_cons.mp hrows
    cases row with
    | nil =>
      exact ih (tag+1) marks htail (fun row hr => hu row (List.mem_cons_of_mem _ hr))
    | cons x xs =>
      have hc : (checkMarks marks marks[x.val] (x :: xs)).1 = true := by
        apply (checkMarks_true marks marks[x.val] (x :: xs)).mpr
        intro y hy
        exact hu (x :: xs) (List.mem_cons_self) y hy x (List.mem_cons_self)
      have hfuture : ∀ row ∈ rows, Uniform (writeMarks tag (x :: xs) marks).1 row := by
        intro row hr
        exact writeMarks_preserves_uniform marks tag (x :: xs) row
          (hu row (List.mem_cons_of_mem _ hr)) (hrel row hr)
      have ht := ih (tag+1) (writeMarks tag (x :: xs) marks).1 htail hfuture
      simpa only [scan,hc,↓reduceIte] using ht

/-- Initialize the mark array and run the executable family check. -/
def check {n : ℕ} (rows : List (List (Fin n))) : Result n :=
  let q := scan 1 rows (Vector.replicate n 0)
  ⟨q.accepted,q.marks,q.accesses+n⟩

theorem check_accepts_of_descending {n : ℕ} (rows : List (List (Fin n)))
    (hrows : DescendingLaminar rows) : (check rows).accepted = true := by
  apply scan_accepts_of_descending 1 rows (Vector.replicate n 0) hrows
  intro row hr x hx y hy
  simp

theorem check_accesses_le {n : ℕ} (rows : List (List (Fin n))) :
    (check rows).accesses ≤ n+4*incidenceCount rows+3*rows.length := by
  have := scan_accesses_le 1 rows (Vector.replicate n 0)
  simp only [check]
  omega

/-- Cardinality order turns ordinary laminarity into the directional condition
needed by the marking algorithm. -/
lemma descending_of_laminar_and_sizes {n : ℕ} (rows : List (List (Fin n)))
    (hnodup : ∀ row ∈ rows, row.Nodup)
    (hsizes : rows.Pairwise (fun a b => b.length ≤ a.length))
    (hlam : rows.Pairwise (fun a b => Disjoint a.toFinset b.toFinset ∨
      a.toFinset ⊆ b.toFinset ∨ b.toFinset ⊆ a.toFinset)) :
    DescendingLaminar rows := by
  apply List.Pairwise.imp_of_mem (R := fun a b => b.length ≤ a.length ∧
    (Disjoint a.toFinset b.toFinset ∨ a.toFinset ⊆ b.toFinset ∨ b.toFinset ⊆ a.toFinset))
      (l := rows) ?_ (hsizes.and hlam)
  intro a b ha hb h
  rcases h.2 with hd | hab | hba
  · right
    intro x hx hxa
    exact Finset.disjoint_left.mp hd (List.mem_toFinset.mpr hxa) (List.mem_toFinset.mpr hx)
  · left
    have hcard : b.toFinset.card ≤ a.toFinset.card := by
      simpa only [List.toFinset_card_of_nodup (hnodup a ha),
        List.toFinset_card_of_nodup (hnodup b hb)] using h.1
    have he := Finset.eq_of_subset_of_card_le hab hcard
    intro x hx
    exact List.mem_toFinset.mp (he ▸ List.mem_toFinset.mpr hx)
  · left
    intro x hx
    exact List.mem_toFinset.mp (hba (List.mem_toFinset.mpr hx))

/-- Source Algorithm 2's acceptance and incidence-linear explicit operation bound
for actual size-ordered laminar input rows. -/
theorem check_laminar_spec {n : ℕ} (rows : List (List (Fin n)))
    (hnodup : ∀ row ∈ rows, row.Nodup)
    (hsizes : rows.Pairwise (fun a b => b.length ≤ a.length))
    (hlam : rows.Pairwise (fun a b => Disjoint a.toFinset b.toFinset ∨
      a.toFinset ⊆ b.toFinset ∨ b.toFinset ⊆ a.toFinset)) :
    (check rows).accepted = true ∧
      (check rows).accesses ≤ n+4*incidenceCount rows+3*rows.length :=
  ⟨check_accepts_of_descending rows (descending_of_laminar_and_sizes rows hnodup hsizes hlam),
    check_accesses_le rows⟩

/-- Distinct marks distinguish every already processed neighborhood membership. -/
def Refines {n : ℕ} (marks : Vector Nat n) (history : List (List (Fin n))) : Prop :=
  ∀ x y : Fin n, marks[x.val] = marks[y.val] →
    ∀ row ∈ history, (x ∈ row ↔ y ∈ row)

/-- Ordinary laminarity of the supplied finite incidence sets. -/
def Laminar {n : ℕ} (rows : List (List (Fin n))) : Prop :=
  rows.Pairwise (fun a b => Disjoint a.toFinset b.toFinset ∨
    a.toFinset ⊆ b.toFinset ∨ b.toFinset ⊆ a.toFinset)

lemma writeMarks_fresh {n : ℕ} (marks : Vector Nat n) (tag : ℕ)
    (row : List (Fin n)) (hf : ∀ x : Fin n, marks[x.val] < tag) :
    ∀ x : Fin n, (writeMarks tag row marks).1[x.val] < tag+1 := by
  intro x
  rw [writeMarks_get]
  split
  · omega
  · exact (hf x).trans (Nat.lt_succ_self tag)

lemma writeMarks_refines {n : ℕ} (marks : Vector Nat n) (tag : ℕ)
    (row : List (Fin n)) (history : List (List (Fin n)))
    (hf : ∀ x : Fin n, marks[x.val] < tag) (hr : Refines marks history)
    (hu : Uniform marks row) : Refines (writeMarks tag row marks).1 (row :: history) := by
  intro x y he b hb
  have hxymem : x ∈ row ↔ y ∈ row := by
    rw [writeMarks_get,writeMarks_get] at he
    have hx := hf x
    have hy := hf y
    by_cases hxm : x ∈ row <;> by_cases hym : y ∈ row <;> simp_all
  have hxy : marks[x.val] = marks[y.val] := by
    by_cases hx : x ∈ row
    · exact hu x hx y (hxymem.mp hx)
    · have hy : y ∉ row := fun h => hx (hxymem.mpr h)
      simpa only [writeMarks_get,if_neg hx,if_neg hy] using he
  rcases List.mem_cons.mp hb with rfl | hb
  · exact hxymem
  · exact hr x y hxy b hb

lemma uniform_relation_history {n : ℕ} (marks : Vector Nat n)
    (row : List (Fin n)) (history : List (List (Fin n)))
    (hr : Refines marks history) (hu : Uniform marks row) :
    ∀ b ∈ history, Disjoint row.toFinset b.toFinset ∨ row.toFinset ⊆ b.toFinset := by
  intro b hb
  cases row with
  | nil => simp
  | cons x xs =>
    by_cases hx : x ∈ b
    · right
      intro y hy
      have hyy : y ∈ x :: xs := List.mem_toFinset.mp hy
      exact List.mem_toFinset.mpr ((hr y x (hu y hyy x (List.mem_cons_self)) b hb).mpr hx)
    · left
      apply Finset.disjoint_left.mpr
      intro y hy hyb
      have hyy : y ∈ x :: xs := List.mem_toFinset.mp hy
      exact hx ((hr y x (hu y hyy x (List.mem_cons_self)) b hb).mp (List.mem_toFinset.mp hyb))

/-- A successful scan proves ordinary laminarity. The invariant accounts for
fresh array tags and all rows that were actually processed. -/
theorem scan_sound {n : ℕ} (tag : ℕ) (rows : List (List (Fin n)))
    (marks : Vector Nat n) (history : List (List (Fin n)))
    (hf : ∀ x : Fin n, marks[x.val] < tag) (hr : Refines marks history)
    (hh : Laminar history) (hok : (scan tag rows marks).accepted = true) :
    Laminar (rows.reverse ++ history) := by
  induction rows generalizing tag marks history with
  | nil => simpa [Laminar] using hh
  | cons row rows ih =>
    cases row with
    | nil =>
      have hf' : ∀ x : Fin n, marks[x.val] < tag+1 := fun x =>
        (hf x).trans (Nat.lt_succ_self tag)
      have hr' : Refines marks ([] :: history) := by
        intro x y he b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · simp
        · exact hr x y he b hb
      have hh' : Laminar ([] :: history) := by
        apply List.pairwise_cons.mpr
        refine ⟨?_,hh⟩
        intro b hb
        exact Or.inl (by simp)
      have ht := ih (tag+1) marks ([] :: history) hf' hr' hh' hok
      simpa [List.reverse_cons,List.append_assoc] using ht
    | cons x xs =>
      have hc : (checkMarks marks marks[x.val] (x :: xs)).1 = true := by
        by_contra hn
        simp [scan,hn] at hok
      have hu : Uniform marks (x :: xs) := by
        have hall := (checkMarks_true marks marks[x.val] (x :: xs)).mp hc
        intro a ha b hb
        exact (hall a ha).trans (hall b hb).symm
      have hh' : Laminar ((x :: xs) :: history) := by
        apply List.pairwise_cons.mpr
        refine ⟨?_,hh⟩
        intro b hb
        rcases uniform_relation_history marks (x :: xs) history hr hu b hb with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      have hok' : (scan (tag+1) rows (writeMarks tag (x :: xs) marks).1).accepted = true := by
        simpa only [scan,hc,↓reduceIte] using hok
      have ht := ih (tag+1) (writeMarks tag (x :: xs) marks).1 ((x :: xs) :: history)
        (writeMarks_fresh marks tag (x :: xs) hf)
        (writeMarks_refines marks tag (x :: xs) history hf hr hu) hh' hok'
      simpa [List.reverse_cons,List.append_assoc] using ht

/-- Every accepted input family really is laminar; no sortedness promise is
needed for this soundness direction. -/
theorem check_sound {n : ℕ} (rows : List (List (Fin n)))
    (hok : (check rows).accepted = true) : Laminar rows := by
  have h := scan_sound 1 rows (Vector.replicate n 0) []
    (by intro x; simp) (by intro x y he row hr; cases hr) (by simp [Laminar]) hok
  simp only [List.append_nil] at h
  have hp := List.pairwise_reverse.mp h
  apply hp.imp
  intro a b hrel
  rcases hrel with hd | h | h
  · exact Or.inl hd.symm
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

/-- Exact correctness of the executable size-ordered marking checker. -/
theorem check_correct {n : ℕ} (rows : List (List (Fin n)))
    (hnodup : ∀ row ∈ rows, row.Nodup)
    (hsizes : rows.Pairwise (fun a b => b.length ≤ a.length)) :
    (check rows).accepted = true ↔ Laminar rows := by
  refine ⟨check_sound rows,?_⟩
  intro hlam
  exact (check_laminar_spec rows hnodup hsizes hlam).1

end LaminarMarking

end HiddenCircuits.DH
