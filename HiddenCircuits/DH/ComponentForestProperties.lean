import HiddenCircuits.DH.ComponentForestCorrectness

namespace HiddenCircuits.DH.ComponentForest
open SimpleGraph

lemma owner_reachable {n : ℕ} {G : SimpleGraph (Fin n)} (rows : Vector (List (Fin n)) n)
    (hr : LinearBuckets.Adjacency.Represents G rows) (v : Fin n) :
    G.Reachable (build rows).owners[v.val] v :=
  ((forest_invariant rows hr).depth v (forest_marked rows hr v)).2

lemma owner_idempotent {n : ℕ} {G : SimpleGraph (Fin n)} (rows : Vector (List (Fin n)) n)
    (hr : LinearBuckets.Adjacency.Represents G rows) (v : Fin n) :
    (build rows).owners[((build rows).owners[v.val]).val]=(build rows).owners[v.val] :=
  (forest_owner_iff rows hr _ _).mpr (owner_reachable rows hr v)

lemma depth_zero_iff_owner {n : ℕ} {G : SimpleGraph (Fin n)} (rows : Vector (List (Fin n)) n)
    (hr : LinearBuckets.Adjacency.Represents G rows) (v : Fin n) :
    (build rows).depths[v.val].val=0 ↔ (build rows).owners[v.val]=v := by
  change (depths (forest rows))[v.val].val=0 ↔ _
  rw [forest_depths rows hr v]
  exact (owner_reachable rows hr v).dist_eq_zero_iff

lemma adjacent_owners {n : ℕ} {G : SimpleGraph (Fin n)} (rows : Vector (List (Fin n)) n)
    (hr : LinearBuckets.Adjacency.Represents G rows) (u v : Fin n) (ha : G.Adj u v) :
    (build rows).owners[u.val]=(build rows).owners[v.val] :=
  (forest_owner_iff rows hr u v).mpr ha.reachable

lemma adjacent_depths {n : ℕ} {G : SimpleGraph (Fin n)} (rows : Vector (List (Fin n)) n)
    (hr : LinearBuckets.Adjacency.Represents G rows) (u v : Fin n) (ha : G.Adj u v) :
    (build rows).depths[u.val].val≤(build rows).depths[v.val].val+1 ∧
      (build rows).depths[v.val].val≤(build rows).depths[u.val].val+1 := by
  have ho := adjacent_owners rows hr u v ha
  change (forest rows).owners[u.val]=(forest rows).owners[v.val] at ho
  change (depths (forest rows))[u.val].val≤(depths (forest rows))[v.val].val+1 ∧
    (depths (forest rows))[v.val].val≤(depths (forest rows))[u.val].val+1
  rw [forest_depths rows hr u,forest_depths rows hr v,ho]
  have h := ha.diff_dist_adj (u:=(forest rows).owners[v.val])
  rcases h with h | h | h <;> omega

end HiddenCircuits.DH.ComponentForest
