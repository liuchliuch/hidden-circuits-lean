import HiddenCircuits.DH.ModuleExecution
import HiddenCircuits.DH.LexBFSInput

/-! Compact induced-subgraph adjacency input using one globally reused epoch/rank workspace.
No whole-graph clearing or whole-graph allocation occurs at a block extraction. -/
namespace HiddenCircuits.DH.InducedInput
open LexBFSPartition LinearBuckets

structure Workspace (n : ℕ) where
  stamp : Vector ℕ n
  rank : Vector ℕ n

def Ready {n : ℕ} (w : Workspace n) (epoch : ℕ) : Prop := ∀ v : Fin n, w.stamp[v.val] < epoch

def initial (n : ℕ) : Counted (Workspace n) := ⟨⟨Vector.replicate n 0,Vector.replicate n 0⟩,2*n⟩

lemma initial_ready (n : ℕ) : Ready (initial n).value 1 := by intro v; simp [initial]

/-- Write compact ranks only at the supplied vertices. -/
def indexFrom {n k : ℕ} (vertices : Vector (Fin n) k) (epoch : ℕ) :
    List (Fin k) → Workspace n → Counted (Workspace n)
  | [],w => ⟨w,0⟩
  | i::indices,w =>
      let v := vertices[i.val]
      let q := indexFrom vertices epoch indices ⟨w.stamp.set v.val epoch,w.rank.set v.val i.val⟩
      ⟨q.value,q.accesses+4⟩

lemma indexFrom_stamp {n k : ℕ} (vertices : Vector (Fin n) k) (epoch : ℕ)
    (indices : List (Fin k)) (w : Workspace n) (v : Fin n) :
    (indexFrom vertices epoch indices w).value.stamp[v.val] =
      if v∈indices.map (fun i => vertices[i.val]) then epoch else w.stamp[v.val] := by
  induction indices generalizing w with
  | nil => simp [indexFrom]
  | cons i indices ih =>
    simp only [indexFrom,ih,List.map_cons,List.mem_cons]
    by_cases hv : v=vertices[i.val]
    · subst v; simp
    · have hiv : (vertices[i.val]).val≠v.val := fun he => hv (Fin.ext he).symm
      simp [hv,hiv]

lemma indexFrom_rank {n k : ℕ} (vertices : Vector (Fin n) k)
    (hinj : Function.Injective (fun i : Fin k => vertices[i.val])) (epoch : ℕ)
    (indices : List (Fin k)) (w : Workspace n) (i : Fin k) :
    (indexFrom vertices epoch indices w).value.rank[(vertices[i.val]).val] =
      if i∈indices then i.val else w.rank[(vertices[i.val]).val] := by
  induction indices generalizing w with
  | nil => simp [indexFrom]
  | cons j indices ih =>
    simp only [indexFrom,ih,List.mem_cons]
    by_cases hi : i∈indices
    · simp [hi]
    · by_cases hij : i=j
      · subst j; simp [hi]
      · have hji : (vertices[j.val]).val≠(vertices[i.val]).val := fun he => hij (hinj (Fin.ext he)).symm
        simp [hi,hij,hji]

@[simp] lemma indexFrom_accesses {n k : ℕ} (vertices : Vector (Fin n) k) (epoch : ℕ)
    (indices : List (Fin k)) (w : Workspace n) :
    (indexFrom vertices epoch indices w).accesses = 4*indices.length := by
  induction indices generalizing w <;> simp [indexFrom, *] <;> omega

lemma indexFrom_ready {n k : ℕ} (vertices : Vector (Fin n) k) (epoch : ℕ)
    (indices : List (Fin k)) (w : Workspace n) (hw : Ready w epoch) :
    Ready (indexFrom vertices epoch indices w).value (epoch+1) := by
  intro v
  rw [indexFrom_stamp]
  split_ifs
  · exact Nat.lt_succ_self _
  · exact (hw v).trans (Nat.lt_succ_self _)

/-- Stale marks are ignored; a successful current-epoch lookup reads its compact rank.
The bound guard makes the code total, and is proved successful for indexed vertices. -/
def filterRow {n : ℕ} (k epoch : ℕ) (w : Workspace n) : List (Fin n) → Counted (List (Fin k))
  | [] => ⟨[],0⟩
  | v::vs =>
      let q := filterRow k epoch w vs
      if w.stamp[v.val]=epoch then
        if hv : w.rank[v.val] < k then ⟨⟨w.rank[v.val],hv⟩::q.value,q.accesses+5⟩
        else ⟨q.value,q.accesses+3⟩
      else ⟨q.value,q.accesses+2⟩

lemma filterRow_mem {n k : ℕ} (epoch : ℕ) (w : Workspace n) (vs : List (Fin n)) (i : Fin k) :
    i∈(filterRow k epoch w vs).value ↔
      ∃ v∈vs, w.stamp[v.val]=epoch ∧ w.rank[v.val]=i.val := by
  induction vs with
  | nil => simp [filterRow]
  | cons v vs ih =>
    by_cases he : w.stamp[v.val]=epoch
    · by_cases hv : w.rank[v.val]<k
      · simp only [filterRow,he,hv,↓reduceIte,↓reduceDIte,List.mem_cons,ih]
        constructor
        · rintro (hi | hi)
          · exact ⟨v,Or.inl rfl,he,(congrArg Fin.val hi).symm⟩
          · obtain ⟨u,hu,hs,hr⟩ := hi
            exact ⟨u,Or.inr hu,hs,hr⟩
        · rintro ⟨u,hu,hs,hr⟩
          rcases hu with rfl | hu
          · exact Or.inl (Fin.ext hr.symm)
          · exact Or.inr ⟨u,hu,hs,hr⟩
      · simp only [filterRow,he,hv,↓reduceIte,↓reduceDIte,ih]
        constructor
        · rintro ⟨u,hu,hs,hr⟩; exact ⟨u,List.mem_cons_of_mem _ hu,hs,hr⟩
        · rintro ⟨u,hu,hs,hr⟩
          rcases List.mem_cons.mp hu with rfl | hu
          · have := i.isLt; omega
          · exact ⟨u,hu,hs,hr⟩
    · simp only [filterRow,he,↓reduceIte,ih]
      constructor
      · rintro ⟨u,hu,hs,hr⟩; exact ⟨u,List.mem_cons_of_mem _ hu,hs,hr⟩
      · rintro ⟨u,hu,hs,hr⟩
        rcases List.mem_cons.mp hu with rfl | hu
        · exact False.elim (he hs)
        · exact ⟨u,hu,hs,hr⟩

lemma filterRow_accesses {n k : ℕ} (epoch : ℕ) (w : Workspace n) (vs : List (Fin n)) :
    (filterRow k epoch w vs).accesses ≤ 5*vs.length := by
  induction vs with
  | nil => simp [filterRow]
  | cons v vs ih => simp only [filterRow,List.length_cons]; split_ifs <;> dsimp only <;> (try simp only [List.length_cons]) <;> omega

lemma filterRow_nodup {n k : ℕ} (epoch : ℕ) (w : Workspace n) (vs : List (Fin n))
    (hn : vs.Nodup)
    (hinj : ∀ u v : Fin n, w.stamp[u.val]=epoch → w.stamp[v.val]=epoch →
      w.rank[u.val]=w.rank[v.val] → u=v) : (filterRow k epoch w vs).value.Nodup := by
  induction vs with
  | nil => simp [filterRow]
  | cons v vs ih =>
    obtain ⟨hvn,hn⟩ := List.nodup_cons.mp hn
    simp only [filterRow]
    split_ifs with he hv
    · refine List.nodup_cons.mpr ⟨?_,ih hn⟩
      intro hm
      obtain ⟨u,hu,hs,hr⟩ := (filterRow_mem epoch w vs ⟨w.rank[v.val],hv⟩).mp hm
      have heq := hinj u v hs he hr
      exact hvn (heq ▸ hu)
    · exact ih hn
    · exact ih hn

/-- Current-epoch marks are precisely one compact vertex array and its inverse ranks. -/
structure Indexed {n k : ℕ} (vertices : Vector (Fin n) k) (epoch : ℕ) (w : Workspace n) : Prop where
  stamp : ∀ v, w.stamp[v.val]=epoch ↔ ∃ i : Fin k, vertices[i.val]=v
  rank : ∀ i : Fin k, w.rank[(vertices[i.val]).val]=i.val

lemma indexed_after {n k : ℕ} (vertices : Vector (Fin n) k)
    (hinj : Function.Injective (fun i : Fin k => vertices[i.val])) (epoch : ℕ) (w : Workspace n)
    (hw : Ready w epoch) : Indexed vertices epoch (indexFrom vertices epoch (List.finRange k) w).value := by
  constructor
  · intro v
    rw [indexFrom_stamp]
    by_cases hv : v∈(List.finRange k).map (fun i => vertices[i.val])
    · simp only [hv,↓reduceIte]
      obtain ⟨i,hi,he⟩ := List.mem_map.mp hv
      exact ⟨fun _ => ⟨i,he⟩,fun _ => trivial⟩
    · have he : w.stamp[v.val]≠epoch := Nat.ne_of_lt (hw v)
      simp only [hv,↓reduceIte,he,false_iff,not_exists]
      intro i hi
      exact hv (List.mem_map.mpr ⟨i,List.mem_finRange i,hi⟩)
  · intro i
    simpa using indexFrom_rank vertices hinj epoch (List.finRange k) w i

lemma Indexed.rank_injective {n k : ℕ} {vertices : Vector (Fin n) k} {epoch : ℕ} {w : Workspace n}
    (h : Indexed vertices epoch w) {u v : Fin n} (hu : w.stamp[u.val]=epoch)
    (hv : w.stamp[v.val]=epoch) (he : w.rank[u.val]=w.rank[v.val]) : u=v := by
  obtain ⟨i,rfl⟩ := (h.stamp u).mp hu
  obtain ⟨j,rfl⟩ := (h.stamp v).mp hv
  rw [h.rank,h.rank] at he
  exact congrArg (fun i : Fin k => vertices[i.val]) (Fin.ext he)

lemma Indexed.filterRow_mem {n k : ℕ} {vertices : Vector (Fin n) k} {epoch : ℕ} {w : Workspace n}
    (h : Indexed vertices epoch w) (vs : List (Fin n)) (i : Fin k) :
    i∈(filterRow k epoch w vs).value ↔ vertices[i.val]∈vs := by
  rw [InducedInput.filterRow_mem]
  constructor
  · rintro ⟨v,hv,hs,hr⟩
    obtain ⟨j,rfl⟩ := (h.stamp v).mp hs
    rw [h.rank] at hr
    have he : j=i := Fin.ext hr
    exact he ▸ hv
  · intro hv
    exact ⟨vertices[i.val],hv,(h.stamp _).mpr ⟨i,rfl⟩,h.rank i⟩

lemma vector_values {n k : ℕ} (vertices : Vector (Fin n) k) :
    (List.finRange k).map (fun i => vertices[i.val]) = vertices.toList := by
  rw [← List.ofFn_eq_map]
  simpa only [Vector.toList_ofFn] using congrArg Vector.toList (Vector.ofFn_getElem (xs := vertices))

lemma vector_injective {n k : ℕ} (vertices : Vector (Fin n) k) (hn : vertices.toList.Nodup) :
    Function.Injective (fun i : Fin k => vertices[i.val]) := by
  have he := vector_values vertices
  rw [← he,← List.ofFn_eq_map] at hn
  exact List.nodup_ofFn.mp hn

/-- Scan original rows only at the block vertices, producing compact local adjacency lists. -/
def rowsFrom {n k : ℕ} (vertices : Vector (Fin n) k) (rows : Vector (List (Fin n)) n)
    (epoch : ℕ) (w : Workspace n) : List (Fin k) → Counted (List (List (Fin k)))
  | [] => ⟨[],0⟩
  | i::indices =>
      let row := filterRow k epoch w rows[(vertices[i.val]).val]
      let q := rowsFrom vertices rows epoch w indices
      ⟨row.value::q.value,row.accesses+q.accesses+3⟩

@[simp] lemma rowsFrom_values {n k : ℕ} (vertices : Vector (Fin n) k) (rows : Vector (List (Fin n)) n)
    (epoch : ℕ) (w : Workspace n) (indices : List (Fin k)) :
    (rowsFrom vertices rows epoch w indices).value =
      indices.map (fun i => (filterRow k epoch w rows[(vertices[i.val]).val]).value) := by
  induction indices <;> simp [rowsFrom, *]

lemma rowsFrom_accesses {n k : ℕ} (vertices : Vector (Fin n) k) (rows : Vector (List (Fin n)) n)
    (epoch : ℕ) (w : Workspace n) (indices : List (Fin k)) :
    (rowsFrom vertices rows epoch w indices).accesses ≤
      5*(indices.map (fun i => rows[(vertices[i.val]).val].length)).sum+3*indices.length := by
  induction indices with
  | nil => simp [rowsFrom]
  | cons i indices ih =>
    have h := filterRow_accesses (k := k) epoch w rows[(vertices[i.val]).val]
    simp only [rowsFrom,List.map_cons,List.sum_cons,List.length_cons]
    omega

structure Prepared (n k : ℕ) where
  workspace : Workspace n
  vertices : Vector (Fin n) k
  rows : Vector (List (Fin k)) k
  accesses : ℕ

/-- Only local-size arrays are allocated here. The original-size rank/stamp arrays are reused. -/
def prepare {n : ℕ} (rows : Vector (List (Fin n)) n) (vertices : List (Fin n))
    (epoch : ℕ) (w : Workspace n) : Prepared n vertices.length :=
  let k := vertices.length
  let labels : Vector (Fin n) k := ⟨vertices.toArray,by simp [k]⟩
  let indices := List.finRange k
  let marked := indexFrom labels epoch indices w
  let q := rowsFrom labels rows epoch marked.value indices
  ⟨marked.value,labels,⟨q.value.toArray,by simp [q,indices,k]⟩,
    marked.accesses+q.accesses+4*k⟩

@[simp] lemma prepare_vertices {n : ℕ} (rows : Vector (List (Fin n)) n) (vertices : List (Fin n))
    (epoch : ℕ) (w : Workspace n) : (prepare rows vertices epoch w).vertices.toList=vertices := by
  simp [prepare]

@[simp] lemma prepare_get {n : ℕ} (rows : Vector (List (Fin n)) n) (vertices : List (Fin n))
    (epoch : ℕ) (w : Workspace n) (i : Fin vertices.length) :
    (prepare rows vertices epoch w).rows[i.val] =
      (filterRow vertices.length epoch (prepare rows vertices epoch w).workspace
        rows[((prepare rows vertices epoch w).vertices[i.val]).val]).value := by
  simp [prepare]

lemma prepare_indexed {n : ℕ} (rows : Vector (List (Fin n)) n) (vertices : List (Fin n))
    (epoch : ℕ) (w : Workspace n) (hw : Ready w epoch) (hn : vertices.Nodup) :
    Indexed (prepare rows vertices epoch w).vertices epoch (prepare rows vertices epoch w).workspace := by
  apply indexed_after
  · apply vector_injective
    simpa using hn
  · exact hw

lemma prepare_ready {n : ℕ} (rows : Vector (List (Fin n)) n) (vertices : List (Fin n))
    (epoch : ℕ) (w : Workspace n) (hw : Ready w epoch) :
    Ready (prepare rows vertices epoch w).workspace (epoch+1) :=
  indexFrom_ready _ _ _ _ hw

/-- The prepared rows represent exactly the induced original graph on the compact vertex array. -/
theorem prepare_represents {n : ℕ} (G : SimpleGraph (Fin n))
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (vertices : List (Fin n)) (epoch : ℕ) (w : Workspace n) (hw : Ready w epoch) (hn : vertices.Nodup) :
    Adjacency.Represents (G.comap (fun i : Fin vertices.length => (prepare rows vertices epoch w).vertices[i.val]))
      (prepare rows vertices epoch w).rows := by
  intro i j
  rw [prepare_get,(prepare_indexed rows vertices epoch w hw hn).filterRow_mem,hr]
  rfl

lemma prepare_nodup {n : ℕ} (rows : Vector (List (Fin n)) n)
    (hr : ∀ v : Fin n, rows[v.val].Nodup) (vertices : List (Fin n)) (epoch : ℕ)
    (w : Workspace n) (hw : Ready w epoch) (hn : vertices.Nodup) :
    ∀ i : Fin vertices.length, ((prepare rows vertices epoch w).rows[i.val]).Nodup := by
  intro i
  rw [prepare_get]
  apply filterRow_nodup _ _ _ (hr _)
  intro u v hu hv he
  exact (prepare_indexed rows vertices epoch w hw hn).rank_injective hu hv he

/-- Every original incidence of a supplied block vertex is scanned only once, with no O(n)
term per call. The four local-size overheads include length, labels, indices and result-array copies. -/
theorem prepare_accesses {n : ℕ} (rows : Vector (List (Fin n)) n) (vertices : List (Fin n))
    (epoch : ℕ) (w : Workspace n) :
    (prepare rows vertices epoch w).accesses ≤
      11*vertices.length+5*(vertices.map (fun v => rows[v.val].length)).sum := by
  let labels : Vector (Fin n) vertices.length := ⟨vertices.toArray,by simp⟩
  let marked := indexFrom labels epoch (List.finRange vertices.length) w
  have h := rowsFrom_accesses labels rows epoch marked.value (List.finRange vertices.length)
  have hl : ((List.finRange vertices.length).map (fun i => rows[(labels[i.val]).val].length)).sum =
      (vertices.map (fun v => rows[v.val].length)).sum := by
    have he := congrArg (List.map (fun v : Fin n => rows[v.val].length)) (vector_values labels)
    simp only [List.map_map,Function.comp_def] at he
    exact congrArg List.sum he
  rw [hl,List.length_finRange] at h
  change (indexFrom labels epoch (List.finRange vertices.length) w).accesses+
    (rowsFrom labels rows epoch marked.value (List.finRange vertices.length)).accesses+4*vertices.length ≤ _
  rw [indexFrom_accesses,List.length_finRange]
  omega

lemma prepare_injective {n : ℕ} (rows : Vector (List (Fin n)) n) (vertices : List (Fin n))
    (epoch : ℕ) (w : Workspace n) (hn : vertices.Nodup) :
    Function.Injective (fun i : Fin vertices.length => (prepare rows vertices epoch w).vertices[i.val]) := by
  apply vector_injective
  simpa using hn

lemma prepare_image {n : ℕ} (rows : Vector (List (Fin n)) n) (vertices : List (Fin n))
    (epoch : ℕ) (w : Workspace n) (v : Fin n) :
    (∃ i : Fin vertices.length, (prepare rows vertices epoch w).vertices[i.val]=v) ↔ v∈vertices := by
  have he := vector_values (prepare rows vertices epoch w).vertices
  rw [prepare_vertices] at he
  have hm : v∈(List.finRange vertices.length).map (fun i => (prepare rows vertices epoch w).vertices[i.val]) ↔
      v∈vertices := Iff.of_eq (congrArg (fun xs : List (Fin n) => v∈xs) he)
  exact (by simp only [List.mem_map,List.mem_finRange,true_and] :
    (∃ i : Fin vertices.length, (prepare rows vertices epoch w).vertices[i.val]=v) ↔
      v∈(List.finRange vertices.length).map (fun i => (prepare rows vertices epoch w).vertices[i.val])).trans hm

/-- Return local cotree labels to original vertices using the actual compact vertex array. -/
def restoreTree {n k : ℕ} (vertices : Vector (Fin n) k) :
    LabeledCographTree (Fin k) → Counted (LabeledCographTree (Fin n))
  | .leaf i => ⟨.leaf vertices[i.val],2⟩
  | .node b l r =>
      let x := restoreTree vertices l
      let y := restoreTree vertices r
      ⟨.node b x.value y.value,x.accesses+y.accesses+2⟩

@[simp] lemma restoreTree_value {n k : ℕ} (vertices : Vector (Fin n) k) (t : LabeledCographTree (Fin k)) :
    (restoreTree vertices t).value = t.mapLabels (fun i => vertices[i.val]) := by
  induction t <;> simp [restoreTree,LabeledCographTree.mapLabels, *]

lemma restoreTree_accesses {n k : ℕ} (vertices : Vector (Fin n) k) (t : LabeledCographTree (Fin k)) :
    (restoreTree vertices t).accesses = 2*t.shape.nodes := by
  induction t <;> simp [restoreTree,LabeledCographTree.shape,CographTree.nodes, *] <;> omega

/-- A local ordinary-input cotree is lifted to an actual original-label cotree for the block. -/
theorem restoreTree_spec {n : ℕ} (G : SimpleGraph (Fin n)) (rows : Vector (List (Fin n)) n)
    (vertices : List (Fin n)) (epoch : ℕ) (w : Workspace n) (hn : vertices.Nodup)
    (t : LabeledCographTree (Fin vertices.length)) (htN : t.leaves.Nodup)
    (htC : t.Correct (G.comap (fun i : Fin vertices.length => (prepare rows vertices epoch w).vertices[i.val])))
    (htAll : ∀ i : Fin vertices.length, i∈t.leaves) :
    let out := (restoreTree (prepare rows vertices epoch w).vertices t).value
    out.Correct G ∧ out.leaves.Nodup ∧ ∀ v, v∈out.leaves ↔ v∈vertices := by
  simp only [restoreTree_value]
  refine ⟨LabeledCographTree.Correct.mapLabels _ _ htC (by intro a ha b hb; rfl),?_,?_⟩
  · rw [LabeledCographTree.mapLabels_leaves]
    exact htN.map (prepare_injective rows vertices epoch w hn)
  · intro v
    rw [LabeledCographTree.mapLabels_leaves,List.mem_map,← prepare_image rows vertices epoch w v]
    exact ⟨fun ⟨i,hi,hiv⟩ => ⟨i,hiv⟩,fun ⟨i,hiv⟩ => ⟨i,htAll i,hiv⟩⟩

lemma filterRow_length {n k : ℕ} (epoch : ℕ) (w : Workspace n) (vs : List (Fin n)) :
    (filterRow k epoch w vs).value.length ≤ vs.length := by
  induction vs with
  | nil => simp [filterRow]
  | cons v vs ih => simp only [filterRow,List.length_cons]; split_ifs <;> dsimp only <;> (try simp only [List.length_cons]) <;> omega

lemma incidence_eq_row_sum {n : ℕ} (rows : Vector (List (Fin n)) n) :
    Adjacency.incidenceCount rows = (rows.toList.map List.length).sum := by
  have hv : (List.finRange n).map (fun i => rows[i.val]) = rows.toList := by
    rw [← List.ofFn_eq_map]
    simpa only [Vector.toList_ofFn] using congrArg Vector.toList (Vector.ofFn_getElem (xs := rows))
  have h := congrArg (fun xs : List (List (Fin n)) => (xs.map List.length).sum) hv
  simpa only [List.map_map,Function.comp_def,Adjacency.incidenceCount,Adjacency.entriesFrom_values,
    List.length_flatMap,List.length_map] using h

lemma rowsFrom_length_sum {n k : ℕ} (vertices : Vector (Fin n) k) (rows : Vector (List (Fin n)) n)
    (epoch : ℕ) (w : Workspace n) (indices : List (Fin k)) :
    ((rowsFrom vertices rows epoch w indices).value.map List.length).sum ≤
      (indices.map (fun i => rows[(vertices[i.val]).val].length)).sum := by
  induction indices with
  | nil => simp [rowsFrom]
  | cons i indices ih =>
    have hh := filterRow_length (k := k) epoch w rows[(vertices[i.val]).val]
    simp only [rowsFrom,List.map_cons,List.sum_cons]
    omega

/-- Compact adjacency storage contains only scanned original incidences. -/
theorem prepare_incidence_le {n : ℕ} (rows : Vector (List (Fin n)) n) (vertices : List (Fin n))
    (epoch : ℕ) (w : Workspace n) :
    Adjacency.incidenceCount (prepare rows vertices epoch w).rows ≤
      (vertices.map (fun v => rows[v.val].length)).sum := by
  let labels : Vector (Fin n) vertices.length := ⟨vertices.toArray,by simp⟩
  let marked := indexFrom labels epoch (List.finRange vertices.length) w
  have h := rowsFrom_length_sum labels rows epoch marked.value (List.finRange vertices.length)
  have hl : ((List.finRange vertices.length).map (fun i => rows[(labels[i.val]).val].length)).sum =
      (vertices.map (fun v => rows[v.val].length)).sum := by
    have he := congrArg (List.map (fun v : Fin n => rows[v.val].length)) (vector_values labels)
    simp only [List.map_map,Function.comp_def] at he
    exact congrArg List.sum he
  rw [hl] at h
  rw [incidence_eq_row_sum]
  exact h

end HiddenCircuits.DH.InducedInput

