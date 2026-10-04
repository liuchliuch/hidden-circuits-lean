import HiddenCircuits.DH.LexBFSSemantics

/-! Linear ordinary-input preparation for the stable LexBFS engine.
The engine uses numeric tie ranks; both directions of the permutation are direct arrays. -/
namespace HiddenCircuits.DH.LexBFSInput
open LinearBuckets

structure Order (n : ℕ) where
  vertexAt : Vector (Fin n) n
  rankOf : Vector (Fin n) n
  rank_vertex : ∀ i : Fin n, rankOf[(vertexAt[i.val]).val] = i
  vertex_rank : ∀ v : Fin n, vertexAt[(rankOf[v.val]).val] = v

/-- The actual array lookup functions define the relabeling isomorphism. -/
def Order.equiv {n : ℕ} (o : Order n) : Fin n ≃ Fin n where
  toFun i := o.vertexAt[i.val]
  invFun v := o.rankOf[v.val]
  left_inv := o.rank_vertex
  right_inv := o.vertex_rank

/-- Build the inverse by one direct write per position. -/
def inverseFrom {n : ℕ} (tau : Vector (Fin n) n) :
    List (Fin n) → Vector (Fin n) n → Vector (Fin n) n × ℕ
  | [],inv => (inv,0)
  | i::indices,inv =>
      let q := inverseFrom tau indices (inv.set (tau[i.val]).val i)
      (q.1,q.2+3)

lemma inverseFrom_get {n : ℕ} (tau : Vector (Fin n) n)
    (hinj : Function.Injective (fun i : Fin n => tau[i.val]))
    (indices : List (Fin n)) (inv : Vector (Fin n) n) (i : Fin n) :
    (inverseFrom tau indices inv).1[(tau[i.val]).val] =
      if i ∈ indices then i else inv[(tau[i.val]).val] := by
  induction indices generalizing inv with
  | nil => simp [inverseFrom]
  | cons j indices ih =>
    simp only [inverseFrom,ih]
    by_cases hi : i ∈ indices
    · simp [hi]
    · by_cases hij : i=j
      · subst j; simp [hi]
      · have hji : (tau[j.val]).val ≠ (tau[i.val]).val :=
          fun he => hij (hinj (Fin.ext he)).symm
        simp [hi,hij,hji]

@[simp] lemma inverseFrom_accesses {n : ℕ} (tau : Vector (Fin n) n)
    (indices : List (Fin n)) (inv : Vector (Fin n) n) :
    (inverseFrom tau indices inv).2 = 3*indices.length := by
  induction indices generalizing inv <;> simp [inverseFrom, *] <;> omega

structure OrderResult (n : ℕ) where
  order : Order n
  accesses : ℕ

/-- Initializing and filling the inverse requires no search through the permutation. -/
def ofVector {n : ℕ} (tau : Vector (Fin n) n)
    (hbij : Function.Bijective (fun i : Fin n => tau[i.val])) : OrderResult n :=
  let q := inverseFrom tau (List.finRange n) (Vector.ofFn id)
  have hi : ∀ i : Fin n, q.1[(tau[i.val]).val] = i := by
    intro i
    simpa [q] using inverseFrom_get tau hbij.1 (List.finRange n) (Vector.ofFn id) i
  have hv : ∀ v : Fin n, tau[(q.1[v.val]).val] = v := by
    intro v
    obtain ⟨i,rfl⟩ := hbij.2 v
    exact congrArg (fun j : Fin n => tau[j.val]) (hi i)
  ⟨⟨tau,q.1,hi,hv⟩,q.2+2*n⟩

@[simp] theorem ofVector_accesses {n : ℕ} (tau : Vector (Fin n) n)
    (hbij : Function.Bijective (fun i : Fin n => tau[i.val])) :
    (ofVector tau hbij).accesses = 5*n := by
  simp [ofVector]; omega

/-- Scan a row once, replacing every original vertex by its direct-array tie rank. -/
def rankRow {n : ℕ} (o : Order n) : List (Fin n) → List (Fin n) × ℕ
  | [] => ([],0)
  | v::vs => let q := rankRow o vs; (o.rankOf[v.val]::q.1,q.2+2)

@[simp] lemma rankRow_values {n : ℕ} (o : Order n) (vs : List (Fin n)) :
    (rankRow o vs).1 = vs.map (fun v => o.rankOf[v.val]) := by
  induction vs <;> simp [rankRow, *]

@[simp] lemma rankRow_accesses {n : ℕ} (o : Order n) (vs : List (Fin n)) :
    (rankRow o vs).2 = 2*vs.length := by
  induction vs <;> simp [rankRow, *] <;> omega

/-- Source rows are visited in the requested tie order, and endpoints become numeric ranks. -/
def relabelFrom {n : ℕ} (o : Order n) (rows : Vector (List (Fin n)) n) :
    List (Fin n) → List (List (Fin n)) × ℕ
  | [] => ([],0)
  | i::indices =>
      let row := rankRow o rows[(o.vertexAt[i.val]).val]
      let q := relabelFrom o rows indices
      (row.1::q.1,row.2+q.2+4)

@[simp] lemma relabelFrom_values {n : ℕ} (o : Order n) (rows : Vector (List (Fin n)) n)
    (indices : List (Fin n)) :
    (relabelFrom o rows indices).1 =
      indices.map (fun i => rows[(o.vertexAt[i.val]).val].map (fun v => o.rankOf[v.val])) := by
  induction indices <;> simp [relabelFrom, *]

lemma relabelFrom_accesses {n : ℕ} (o : Order n) (rows : Vector (List (Fin n)) n)
    (indices : List (Fin n)) :
    (relabelFrom o rows indices).2 =
      2*(indices.map (fun i => rows[(o.vertexAt[i.val]).val].length)).sum+4*indices.length := by
  induction indices <;> simp [relabelFrom, *] <;> omega

/-- Relabel without materializing an adjacency matrix. -/
def relabel {n : ℕ} (o : Order n) (rows : Vector (List (Fin n)) n) : Adjacency.Result n :=
  let q := relabelFrom o rows (List.finRange n)
  ⟨⟨q.1.toArray,by simp [q]⟩,q.2+n⟩

@[simp] lemma relabel_get {n : ℕ} (o : Order n) (rows : Vector (List (Fin n)) n) (i : Fin n) :
    (relabel o rows).rows[i.val] = rows[(o.vertexAt[i.val]).val].map (fun v => o.rankOf[v.val]) := by
  simp [relabel]

/-- Rank coordinates do not change any original graph adjacency. -/
theorem relabel_represents {n : ℕ} (o : Order n) (G : SimpleGraph (Fin n))
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows) :
    Adjacency.Represents (G.comap o.equiv) (relabel o rows).rows := by
  intro i j
  rw [relabel_get,List.mem_map]
  constructor
  · rintro ⟨v,hv,he⟩
    have hev : v = o.equiv j := by
      change o.equiv.symm v = j at he
      exact (o.equiv.apply_eq_iff_eq_symm_apply).mpr he.symm |>.symm
    subst v
    exact (hr _ _).mp hv
  · intro hj
    exact ⟨o.equiv j,(hr _ _).mpr hj,o.rank_vertex j⟩

lemma relabel_nodup {n : ℕ} (o : Order n) (rows : Vector (List (Fin n)) n)
    (hn : ∀ i : Fin n, (rows[i.val]).Nodup) (i : Fin n) :
    ((relabel o rows).rows[i.val]).Nodup := by
  rw [relabel_get]
  exact (hn (o.equiv i)).map o.equiv.symm.injective

lemma relabel_sum {n : ℕ} (o : Order n) (rows : Vector (List (Fin n)) n) :
    ((List.finRange n).map (fun i => rows[(o.vertexAt[i.val]).val].length)).sum =
      Adjacency.incidenceCount rows := by
  have hp := (Equiv.Perm.map_finRange_perm o.equiv).map (fun i => rows[i.val].length)
  simp only [List.map_map,Function.comp_def] at hp
  change ((List.finRange n).map (fun i => rows[(o.equiv i).val].length)).sum = _
  rw [hp.sum_eq]
  simp [Adjacency.incidenceCount,Adjacency.entriesFrom_values,List.length_flatMap]

/-- Literal relabeling loops take linear work in the ordinary incidence representation. -/
theorem relabel_accesses {n : ℕ} (o : Order n) (rows : Vector (List (Fin n)) n) :
    (relabel o rows).accesses = 2*Adjacency.incidenceCount rows+5*n := by
  simp [relabel,relabelFrom_accesses,relabel_sum]; omega

lemma relabel_incidence {n : ℕ} (o : Order n) (rows : Vector (List (Fin n)) n) :
    Adjacency.incidenceCount (relabel o rows).rows = Adjacency.incidenceCount rows := by
  simp only [Adjacency.incidenceCount,Adjacency.entriesFrom_values,List.length_flatMap,List.length_map]
  simp only [relabel_get,List.length_map]
  simpa only [Adjacency.incidenceCount,Adjacency.entriesFrom_values,List.length_flatMap,List.length_map]
    using relabel_sum o rows

/-- Fully sorted rank-coordinate rows, from ordinary unordered adjacency lists. -/
def normalize {n : ℕ} (o : Order n) (rows : Vector (List (Fin n)) n) : Adjacency.Result n :=
  let q := relabel o rows
  let t := Adjacency.transpose q.rows
  ⟨t.rows,q.accesses+t.accesses⟩

/-- Linear normalization preserves the actual relabeled graph and produces duplicate-free,
increasing rows for the sparse pointer engine. -/
theorem normalize_spec {n : ℕ} (o : Order n) (G : SimpleGraph (Fin n))
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀ i : Fin n, (rows[i.val]).Nodup) :
    Adjacency.Represents (G.comap o.equiv) (normalize o rows).rows ∧
      (∀ i : Fin n, ((normalize o rows).rows[i.val]).Nodup ∧
        ((normalize o rows).rows[i.val]).Pairwise (· < ·)) ∧
      (normalize o rows).accesses = 9*Adjacency.incidenceCount rows+11*n := by
  have hrep := relabel_represents o G rows hr
  have hnd := relabel_nodup o rows hn
  refine ⟨Adjacency.transpose_represents _ _ hrep,?_,?_⟩
  · intro i
    have hdup := Adjacency.transpose_nodup (relabel o rows).rows hnd i
    have hsort := Adjacency.transpose_sorted (relabel o rows).rows i
    exact ⟨hdup,(hsort.and hdup).imp (fun {u v} h => lt_of_le_of_ne h.1 h.2)⟩
  · change (relabel o rows).accesses+(Adjacency.transpose (relabel o rows).rows).accesses = _
    rw [relabel_accesses,Adjacency.transpose_accesses,relabel_incidence]
    omega

/-- Turn an explicit output list into the forward array, without looking up ranks by search. -/
def vectorOfList {n : ℕ} (tie : List (Fin n)) (hp : tie.Perm (List.finRange n)) : Vector (Fin n) n :=
  ⟨tie.toArray,by simpa using hp.length_eq⟩

lemma vectorOfList_bijective {n : ℕ} (tie : List (Fin n)) (hp : tie.Perm (List.finRange n)) :
    Function.Bijective (fun i : Fin n => (vectorOfList tie hp)[i.val]) := by
  have hlen : tie.length = n := by simpa using hp.length_eq
  have hnd : tie.Nodup := hp.nodup_iff.mpr (List.nodup_finRange n)
  constructor
  · intro i j he
    apply Fin.ext
    apply List.getElem?_inj (show i.val < tie.length by omega) hnd
    have hi : i.val < tie.length := by omega
    have hj : j.val < tie.length := by omega
    simpa only [List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj] using congrArg some he
  · intro v
    obtain ⟨i,hi,hget⟩ := List.mem_iff_getElem.mp (hp.mem_iff.mpr (List.mem_finRange v))
    refine ⟨⟨i,by omega⟩,?_⟩
    simpa [vectorOfList] using hget

/-- An ordinary sweep output list has a certified pair of inverse arrays in linear time. -/
def ofList {n : ℕ} (tie : List (Fin n)) (hp : tie.Perm (List.finRange n)) : OrderResult n :=
  let q := ofVector (vectorOfList tie hp) (vectorOfList_bijective tie hp)
  ⟨q.order,q.accesses+n⟩

@[simp] theorem ofList_accesses {n : ℕ} (tie : List (Fin n)) (hp : tie.Perm (List.finRange n)) :
    (ofList tie hp).accesses = 6*n := by simp [ofList]; omega

@[simp] theorem ofList_vertexAt {n : ℕ} (tie : List (Fin n)) (hp : tie.Perm (List.finRange n)) :
    (ofList tie hp).order.vertexAt.toList = tie := by simp [ofList,ofVector,vectorOfList]

lemma Order.vertexAt_list {n : ℕ} (o : Order n) :
    o.vertexAt.toList = (List.finRange n).map o.equiv := by
  rw [← List.ofFn_eq_map]
  have h := congrArg Vector.toList (Vector.ofFn_getElem (xs := o.vertexAt))
  simpa only [Vector.toList_ofFn] using h.symm

/-- Mapping compact rank-coordinate events back through the forward array gives exactly
the ordinary graph sweep in the requested tie order. -/
theorem sweep_in_rank_coordinates {n : ℕ} (o : Order n) (a : Fin n → Fin n → Bool) (first : Bool) :
    LexBFSModel.sweep a first o.vertexAt.toList =
      (LexBFSModel.sweep (fun i j => a (o.equiv i) (o.equiv j)) first (List.finRange n)).map
        (LexBFSModel.Event.map o.equiv) := by
  rw [o.vertexAt_list,LexBFSModel.sweep_map]

lemma incidence_congr {n : ℕ} (rows rows' : Vector (List (Fin n)) n)
    (h : ∀ i : Fin n, rows[i.val].length = rows'[i.val].length) :
    LinearBuckets.Adjacency.incidenceCount rows = LinearBuckets.Adjacency.incidenceCount rows' := by
  simp only [LinearBuckets.Adjacency.incidenceCount,LinearBuckets.Adjacency.entriesFrom_values,
    List.length_flatMap,List.length_map]
  exact congrArg List.sum (List.map_congr_left (fun i _ => h i))

lemma normalize_incidence {n : ℕ} (o : Order n) (G : SimpleGraph (Fin n))
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀ i : Fin n, (rows[i.val]).Nodup) :
    Adjacency.incidenceCount (normalize o rows).rows = Adjacency.incidenceCount rows := by
  have hnorm := normalize_spec o G rows hr hn
  have hrel := relabel_represents o G rows hr
  rw [← relabel_incidence o rows]
  apply incidence_congr
  intro i
  apply List.Perm.length_eq
  apply (List.perm_ext_iff_of_nodup (hnorm.2.1 i).1 (relabel_nodup o rows hn i)).mpr
  intro j
  exact (hnorm.1 i j).trans (hrel i j).symm

end HiddenCircuits.DH.LexBFSInput
