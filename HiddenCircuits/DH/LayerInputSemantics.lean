import HiddenCircuits.DH.LayerInput
import HiddenCircuits.DH.LayerScheduleForest

/-! Exact graph semantics and partition properties of the computed static arrays. -/
namespace HiddenCircuits.DH.LayerInput
open SimpleGraph LinearBuckets LayerScheduleForest

lemma prepare_rooting {n : ℕ} (G : SimpleGraph (Fin n))
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) :
    Rooting G (fun v=>(prepare G rows hr hn).owners[v.val])
      (fun v=>(prepare G rows hr hn).depths[v.val].val) := by
  refine ⟨ComponentForest.owner_reachable rows hr,?_,ComponentForest.forest_depths rows hr⟩
  intro u v huv
  exact (ComponentForest.forest_owner_iff rows hr u v).mpr huv

lemma prepare_previous_mem {n : ℕ} (G : SimpleGraph (Fin n))
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) (u v : Fin n) :
    v∈(prepare G rows hr hn).previous[u.val] ↔
      v∈forestPredecessors G (fun v=>(prepare G rows hr hn).depths[v.val].val) u := by
  rw [prepare_previous,List.mem_filter]
  simp only [decide_eq_true_eq]
  rw [hr u v]
  change (G.Adj u v ∧ _) ↔ (G.Adj v u ∧ _)
  exact and_congr (G.adj_comm u v) Iff.rfl

lemma prepare_previous_ncard {n : ℕ} (G : SimpleGraph (Fin n))
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) (u : Fin n) :
    ((prepare G rows hr hn).previous[u.val]).length=
      (forestPredecessors G (fun v=>(prepare G rows hr hn).depths[v.val].val) u).ncard := by
  have he : (((prepare G rows hr hn).previous[u.val]).toFinset : Set (Fin n))=
      forestPredecessors G (fun v=>(prepare G rows hr hn).depths[v.val].val) u := by
    ext v;rw [Finset.mem_coe,List.mem_toFinset,prepare_previous_mem]
  rw [←he,Set.ncard_coe_finset,List.toFinset_card_of_nodup ((prepare G rows hr hn).previous_nodup u)]

lemma sameDepthGraph_eq {n : ℕ} (G : SimpleGraph (Fin n)) (depths : Vector (Fin (n+1)) n) :
    ComponentForest.sameDepthGraph G depths = LayerSchedule.sameDepthGraph G (fun v=>depths[v.val].val) := by
  ext u v
  exact ComponentForest.sameDepthGraph_adj G depths u v

lemma prepare_component_roots {n : ℕ} (G : SimpleGraph (Fin n))
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) (k : Fin (n+1)) :
    ((prepare G rows hr hn).componentByLevel[k.val]).Nodup ∧
      ∀r, r∈(prepare G rows hr hn).componentByLevel[k.val] ↔
        r∈(ComponentForest.sameDepthForest (prepare G rows hr hn).depths rows).roots ∧
          (prepare G rows hr hn).depths[r.val]=k := by
  let d := (ComponentForest.build rows).depths
  have h := (ComponentForest.sameDepthForest_components G d rows hr).1
  change ((bucketBy d (ComponentForest.sameDepthForest d rows).roots).value[k.val]).Nodup ∧ _
  rw [bucketBy_get]
  refine ⟨h.filter _,?_⟩
  intro r
  change r∈(bucketBy d (ComponentForest.sameDepthForest d rows).roots).value[k.val] ↔ _
  rw [bucketBy_get,List.mem_filter]
  simp only [beq_iff_eq]
  rfl

lemma prepare_component_mem {n : ℕ} (G : SimpleGraph (Fin n))
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) (k : Fin (n+1)) (r : Fin n)
    (hrk : r∈(prepare G rows hr hn).componentByLevel[k.val]) (v : Fin n) :
    v∈(prepare G rows hr hn).components[r.val] ↔
      (LayerSchedule.sameDepthGraph G (fun v=>(prepare G rows hr hn).depths[v.val].val)).Reachable r v := by
  have hm := ((prepare_component_roots G rows hr hn k).2 r).mp hrk
  have h := ((ComponentForest.sameDepthForest_components G (prepare G rows hr hn).depths rows hr).2.2.1 r hm.1).2 v
  rw [sameDepthGraph_eq] at h
  exact h

lemma prepare_component_depth {n : ℕ} (G : SimpleGraph (Fin n))
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) (k : Fin (n+1)) (r : Fin n)
    (hrk : r∈(prepare G rows hr hn).componentByLevel[k.val]) (v : Fin n)
    (hv : v∈(prepare G rows hr hn).components[r.val]) : (prepare G rows hr hn).depths[v.val]=k := by
  have he := LayerSchedule.sameDepthGraph_reachable_depth _ ((prepare_component_mem G rows hr hn k r hrk v).mp hv)
  have hr' := ((prepare_component_roots G rows hr hn k).2 r).mp hrk
  apply Fin.ext
  exact he.symm.trans (congrArg Fin.val hr'.2)

lemma prepare_component_cover {n : ℕ} (G : SimpleGraph (Fin n))
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) (k : Fin (n+1)) (v : Fin n)
    (hv : (prepare G rows hr hn).depths[v.val]=k) :
    ∃r∈(prepare G rows hr hn).componentByLevel[k.val], v∈(prepare G rows hr hn).components[r.val] := by
  let p := prepare G rows hr hn
  let f := ComponentForest.sameDepthForest p.depths rows
  obtain ⟨hr',hm⟩ := (ComponentForest.sameDepthForest_components G p.depths rows hr).2.2.2.2 v
  have reach := ((ComponentForest.sameDepthForest_components G p.depths rows hr).2.2.1 _ hr').2 v |>.mp hm
  rw [sameDepthGraph_eq] at reach
  have hd := LayerSchedule.sameDepthGraph_reachable_depth _ reach
  refine ⟨f.owners[v.val],((prepare_component_roots G rows hr hn k).2 _).mpr ⟨hr',?_⟩,hm⟩
  apply Fin.ext
  exact hd.trans (congrArg Fin.val hv)

lemma indexed_root_owner {n : ℕ} (G : SimpleGraph (Fin n))
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows) (r : Fin n)
    (hr' : r∈(ComponentForest.indexed rows).roots) :
    (ComponentForest.indexed rows).owners[r.val]=r := by
  change r∈(ComponentForest.indexFrom (ComponentForest.forest rows).components (Vector.replicate n [])).roots at hr'
  rw [ComponentForest.indexFrom_roots] at hr'
  obtain ⟨c,hc,he⟩ := List.mem_map.mp hr'
  subst r
  have h := ComponentForest.forest_components rows hr c hc
  exact h.2.2 c.1 ((h.2.1 c.1).mpr (Reachable.refl _))

lemma prepare_component_owner_mem {n : ℕ} (G : SimpleGraph (Fin n))
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) (k : Fin (n+1)) (r : Fin n)
    (hrk : r∈(prepare G rows hr hn).componentByLevel[k.val]) (v : Fin n) :
    (prepare G rows hr hn).componentOwner[v.val]=r ↔ v∈(prepare G rows hr hn).components[r.val] := by
  let p := prepare G rows hr hn
  let f := ComponentForest.sameDepthForest p.depths rows
  have hr' := ((prepare_component_roots G rows hr hn k).2 r).mp hrk
  have hroot : f.owners[r.val]=r := indexed_root_owner
    (ComponentForest.sameDepthGraph G p.depths) (ComponentForest.sameDepthRows p.depths rows).rows
    (ComponentForest.sameDepthRows_represents G p.depths rows hr) r hr'.1
  have hc := (ComponentForest.sameDepthForest_components G p.depths rows hr).2.1 r v
  rw [hroot,eq_comm] at hc
  rw [sameDepthGraph_eq] at hc
  exact hc.trans (prepare_component_mem G rows hr hn k r hrk v).symm

lemma prepare_component_disjoint {n : ℕ} (G : SimpleGraph (Fin n))
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) (k : Fin (n+1)) (r t : Fin n)
    (hrk : r∈(prepare G rows hr hn).componentByLevel[k.val])
    (htk : t∈(prepare G rows hr hn).componentByLevel[k.val])
    (v : Fin n) (hvr : v∈(prepare G rows hr hn).components[r.val])
    (hvt : v∈(prepare G rows hr hn).components[t.val]) : r=t := by
  exact ((prepare_component_owner_mem G rows hr hn k r hrk v).mpr hvr).symm.trans
    ((prepare_component_owner_mem G rows hr hn k t htk v).mpr hvt)

end HiddenCircuits.DH.LayerInput
