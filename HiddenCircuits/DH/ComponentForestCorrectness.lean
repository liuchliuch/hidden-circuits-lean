import HiddenCircuits.DH.ComponentForestScan

/-! Ordinary-input BFS forest correctness and linear global resource bounds,
including shortest-distance arrays reusable by the DH layer scheduler. -/
namespace HiddenCircuits.DH.ComponentForest
open SimpleGraph BreadthFirst

lemma forest_invariant {n : ℕ} {G : SimpleGraph (Fin n)} (rows : Vector (List (Fin n)) n)
    (hr : LinearBuckets.Adjacency.Represents G rows) :
    MarkInvariant G (forest rows).marks (forest rows).owners :=
  (scan_spec rows hr (List.finRange n) _ _ (empty_invariant G)).invariant

lemma forest_marked {n : ℕ} {G : SimpleGraph (Fin n)} (rows : Vector (List (Fin n)) n)
    (hr : LinearBuckets.Adjacency.Represents G rows) (v : Fin n) : (forest rows).marks[v.val]≠none :=
  (scan_spec rows hr (List.finRange n) _ _ (empty_invariant G)).seen v (by simp)

lemma forest_members {n : ℕ} {G : SimpleGraph (Fin n)} (rows : Vector (List (Fin n)) n)
    (hr : LinearBuckets.Adjacency.Represents G rows) (v : Fin n) : v∈members (forest rows) := by
  have h := (scan_spec rows hr (List.finRange n) _ _ (empty_invariant G)).novel v
  apply h.mpr
  exact ⟨by simp,forest_marked rows hr v⟩

lemma forest_nodup {n : ℕ} {G : SimpleGraph (Fin n)} (rows : Vector (List (Fin n)) n)
    (hr : LinearBuckets.Adjacency.Represents G rows) : (members (forest rows)).Nodup :=
  (scan_spec rows hr (List.finRange n) _ _ (empty_invariant G)).nodup

/-- Every original vertex occurs exactly once across all output component lists. -/
theorem forest_perm {n : ℕ} {G : SimpleGraph (Fin n)} (rows : Vector (List (Fin n)) n)
    (hr : LinearBuckets.Adjacency.Represents G rows) : (members (forest rows)).Perm (List.finRange n) := by
  apply (List.perm_ext_iff_of_nodup (forest_nodup rows hr) (List.nodup_finRange n)).mpr
  intro v
  simp [forest_members rows hr v]

/-- A bucket is exactly the graph-theoretic component of its stored root, and
its vertices all have that root in the direct owner array. -/
theorem forest_components {n : ℕ} {G : SimpleGraph (Fin n)} (rows : Vector (List (Fin n)) n)
    (hr : LinearBuckets.Adjacency.Represents G rows) (b : Fin n × List (Fin n))
    (hb : b∈(forest rows).components) :
    b.2.Nodup ∧ (∀v, v∈b.2 ↔ G.Reachable b.1 v) ∧ ∀v∈b.2, (forest rows).owners[v.val]=b.1 :=
  (scan_spec rows hr (List.finRange n) _ _ (empty_invariant G)).blocks b hb

/-- Direct owner equality is exactly connected-component membership. -/
theorem forest_owner_iff {n : ℕ} {G : SimpleGraph (Fin n)} (rows : Vector (List (Fin n)) n)
    (hr : LinearBuckets.Adjacency.Represents G rows) (u v : Fin n) :
    (forest rows).owners[u.val]=(forest rows).owners[v.val] ↔ G.Reachable u v := by
  have h := forest_invariant rows hr
  have hu := forest_marked rows hr u
  have hv := forest_marked rows hr v
  constructor
  · intro he
    have h1 := (h.depth u hu).2
    have h2 := (h.depth v hv).2
    rw [he] at h1
    exact h1.symm.trans h2
  · exact h.owner u v hu hv

/-- Bounded depth conversion is inactive on every reachable component and gives
ordinary graph distance from that component's actual chosen root. -/
theorem forest_depths {n : ℕ} {G : SimpleGraph (Fin n)} (rows : Vector (List (Fin n)) n)
    (hr : LinearBuckets.Adjacency.Represents G rows) (v : Fin n) :
    (depths (forest rows))[v.val].val=G.dist (forest rows).owners[v.val] v := by
  have h := (forest_invariant rows hr).depth v (forest_marked rows hr v)
  have hd := reachable_dist_lt (forest rows).owners[v.val] v h.2
  simp [depths,h.1,Nat.min_eq_left hd.le]

lemma forest_weight {n : ℕ} {G : SimpleGraph (Fin n)} (rows : Vector (List (Fin n)) n)
    (hr : LinearBuckets.Adjacency.Represents G rows) :
    frontierWeight rows (members (forest rows)) = LinearBuckets.Adjacency.incidenceCount rows+n := by
  have h := ((forest_perm rows hr).map (fun v => rows[v.val].length+1)).sum_eq
  change frontierWeight rows (members (forest rows))=frontierWeight rows (List.finRange n) at h
  rw [frontierWeight_eq rows (List.finRange n),neighbors_all_length,List.length_finRange] at h
  exact h

/-- Linear array/list accesses for the entire forest, including one global
initialization and the outer vertex scan, without connectedness assumptions. -/
theorem forest_accesses {n : ℕ} {G : SimpleGraph (Fin n)} (rows : Vector (List (Fin n)) n)
    (hr : LinearBuckets.Adjacency.Represents G rows) :
    (forest rows).accesses ≤ 7*LinearBuckets.Adjacency.incidenceCount rows+16*n+3 := by
  have h := scan_accesses rows (List.finRange n) (Vector.replicate n none) (Vector.ofFn id)
  have hw := forest_weight rows hr
  simp only [forest,members] at hw
  simp only [List.length_finRange,members] at h
  rw [hw] at h
  simp only [forest]
  omega

lemma forest_allocations {n : ℕ} (rows : Vector (List (Fin n)) n) :
    (forest rows).allocations ≤ (forest rows).accesses := by
  have h := scan_allocations rows (List.finRange n) (Vector.replicate n none) (Vector.ofFn id)
  simp only [forest];omega

/-- Final ordinary-input output includes the existing bounded-depth interface. -/
structure Output (n : ℕ) where
  owners : Vector (Fin n) n
  depths : Vector (Fin (n+1)) n
  components : List (Fin n × List (Fin n))
  accesses : ℕ
  allocations : ℕ

def build {n : ℕ} (rows : Vector (List (Fin n)) n) : Output n :=
  let q := forest rows
  ⟨q.owners,depths q,q.components,q.accesses+2*n+1,q.allocations+n⟩

/-- Complete executable forest contract, usable unchanged for filtered adjacency
rows such as the graph retaining only equal-depth edges. -/
theorem build_spec {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : LinearBuckets.Adjacency.Represents G rows)
    (hn : ∀v : Fin n, (rows[v.val]).Nodup) :
    (∀u v, (build rows).owners[u.val]=(build rows).owners[v.val] ↔ G.Reachable u v) ∧
    (∀v, (build rows).depths[v.val].val=G.dist (build rows).owners[v.val] v) ∧
    ((build rows).components.flatMap Prod.snd).Perm (List.finRange n) ∧
    (∀b∈(build rows).components, b.2.Nodup ∧ (∀v, v∈b.2 ↔ G.Reachable b.1 v) ∧
      ∀v∈b.2, (build rows).owners[v.val]=b.1) ∧
    (build rows).accesses ≤ 14*G.edgeFinset.card+18*n+4 ∧
    (build rows).allocations ≤ 14*G.edgeFinset.card+18*n+4 := by
  refine ⟨forest_owner_iff rows hr,forest_depths rows hr,forest_perm rows hr,forest_components rows hr,?_,?_⟩
  · have h := forest_accesses rows hr
    rw [LinearBuckets.Adjacency.incidenceCount_eq_degree_sum G rows hr hn,G.sum_degrees_eq_twice_card_edges] at h
    simp only [build];omega
  · have h := forest_accesses rows hr
    rw [LinearBuckets.Adjacency.incidenceCount_eq_degree_sum G rows hr hn,G.sum_degrees_eq_twice_card_edges] at h
    have ha := forest_allocations rows
    simp only [build];omega

end HiddenCircuits.DH.ComponentForest
