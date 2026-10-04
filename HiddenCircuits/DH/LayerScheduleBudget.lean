import HiddenCircuits.DH.LayerInputSemantics
import HiddenCircuits.DH.LayerStepResources

/-! The static layer schedule scans each original component member once and
each predecessor incidence at most once. All repeated induced extraction is
accounted for separately by the decreasing live-row potential. -/
namespace HiddenCircuits.DH.LayerExecution
open SimpleGraph LexBFSPartition LinearBuckets BlockCollapse LayerInput
open scoped BigOperators

/-- List-loop dispatch is included in these proof-side budgets. -/
def componentBudget {n : ℕ} (p : Prepared n) (k : Fin (n+1)) : ℕ :=
  (p.componentByLevel[k.val].map (fun r=>3*(p.components[r.val]).length+5)).sum

def vertexBudget {n : ℕ} (p : Prepared n) (k : Fin (n+1)) : ℕ :=
  (p.vertexByLevel[k.val].map (fun v=>3*(p.previous[v.val]).length+5)).sum

def levelBudget {n : ℕ} (p : Prepared n) (k : Fin (n+1)) : ℕ :=
  componentBudget p k+vertexBudget p k+4

def prefixBudget {n : ℕ} (p : Prepared n) : (fuel : ℕ)→fuel≤n→ℕ
  | 0,_ => 0
  | k+1,h => prefixBudget p k (by omega)+levelBudget p ⟨k+1,by omega⟩

lemma bucketBy_weight {n : ℕ} (d : Vector (Fin (n+1)) n) (vs : List (Fin n)) (w : Fin n→ℕ) :
    (∑k : Fin (n+1), ((bucketBy d vs).value[k.val].map w).sum)=(vs.map w).sum := by
  simp only [bucketBy_get]
  induction vs with
  | nil => simp
  | cons v vs ih =>
    have he (k : Fin (n+1)) : (((v::vs).filter (fun v=>d[v.val] == k)).map w).sum =
        (if d[v.val]=k then w v else 0)+((vs.filter (fun v=>d[v.val] == k)).map w).sum := by
      by_cases hk : d[v.val]=k <;> simp [hk]
    simp only [he,Finset.sum_add_distrib,ih,List.map_cons,List.sum_cons]
    simp

lemma indexed_flatten_perm {n : ℕ} (G : SimpleGraph (Fin n))
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows) :
    ((ComponentForest.indexed rows).roots.flatMap (fun r=>(ComponentForest.indexed rows).buckets[r.val])).Perm
      (List.finRange n) := by
  let cs := (ComponentForest.forest rows).components
  let idx := ComponentForest.indexFrom cs (Vector.replicate n [])
  have hn := ComponentForest.forest_roots_nodup rows hr
  have hmap : cs.flatMap (fun c=>idx.buckets[c.1.val])=cs.flatMap Prod.snd := by
    apply List.flatMap_congr
    intro c hc
    exact ComponentForest.indexFrom_mem cs (Vector.replicate n []) hn c hc
  change ((ComponentForest.indexFrom cs (Vector.replicate n [])).roots.flatMap
    (fun r=>idx.buckets[r.val])).Perm _
  rw [ComponentForest.indexFrom_roots,List.flatMap_map]
  change (cs.flatMap (fun c=>idx.buckets[c.1.val])).Perm _
  rw [hmap]
  exact ComponentForest.forest_perm rows hr

lemma list_budget {α : Type*} (xs : List α) (f : α→ℕ) :
    (xs.map (fun x=>3*f x+5)).sum=3*(xs.map f).sum+5*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih];omega

lemma componentBudget_sum {n : ℕ} (G : SimpleGraph (Fin n))
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) :
    (∑k : Fin (n+1), componentBudget (prepare G rows hr hn) k)≤8*n := by
  let p := prepare G rows hr hn
  let d := (ComponentForest.build rows).depths
  let comps := ComponentForest.sameDepthForest d rows
  change (∑k : Fin (n+1), (((bucketBy d comps.roots).value[k.val]).map
    (fun r=>3*(comps.buckets[r.val]).length+5)).sum)≤_
  rw [bucketBy_weight,list_budget]
  have hp := indexed_flatten_perm (ComponentForest.sameDepthGraph G d)
    (ComponentForest.sameDepthRows d rows).rows (ComponentForest.sameDepthRows_represents G d rows hr)
  have hl : (comps.roots.map (fun r=>(comps.buckets[r.val]).length)).sum=n := by
    have hh := hp.length_eq
    simpa only [List.length_flatMap,List.length_finRange] using hh
  have hrlen : comps.roots.length≤n := by
    have hh := (ComponentForest.sameDepthForest_components G d rows hr).1.length_le_card
    simpa using hh
  omega

lemma vertexBudget_sum {n : ℕ} (G : SimpleGraph (Fin n))
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) :
    (∑k : Fin (n+1), vertexBudget (prepare G rows hr hn) k)≤3*Adjacency.incidenceCount rows+5*n := by
  let d := (ComponentForest.build rows).depths
  let prev := BreadthFirst.previous d rows
  let keys := LevelOrdering.buildKeys d prev.rows (BreadthFirst.previous_nodup d rows hn)
  let ordered := byPreviousSize keys.keys
  change (∑k : Fin (n+1), (((bucketBy d ordered.value).value[k.val]).map
    (fun v=>3*(prev.rows[v.val]).length+5)).sum)≤_
  rw [bucketBy_weight]
  have hp := (byPreviousSize_perm keys.keys).map (fun v=>3*(prev.rows[v.val]).length+5)
  rw [hp.sum_eq,list_budget,List.length_finRange]
  have he : ((List.finRange n).map (fun v=>prev.rows[v.val].length)).sum=Adjacency.incidenceCount prev.rows := by
    rw [CographFrontend.incidenceCount_eq_sum,←List.ofFn_eq_map,List.sum_ofFn]
  rw [he]
  have hi := BreadthFirst.previous_incidence_le d rows
  change Adjacency.incidenceCount prev.rows≤_ at hi
  omega

lemma levelBudget_sum {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) :
    (∑k : Fin (n+1), levelBudget (prepare G rows hr hn) k)≤6*G.edgeFinset.card+17*n+4 := by
  have hc := componentBudget_sum G rows hr hn
  have hv := vertexBudget_sum G rows hr hn
  rw [Adjacency.incidenceCount_eq_degree_sum G rows hr hn,G.sum_degrees_eq_twice_card_edges] at hv
  simp only [levelBudget,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  omega

lemma prefixBudget_eq {n : ℕ} (p : Prepared n) (fuel : ℕ) (hf : fuel≤n) :
    prefixBudget p fuel hf+levelBudget p 0=
      ∑i : Fin (fuel+1), levelBudget p ⟨i.val,by omega⟩ := by
  induction fuel with
  | zero => simp [prefixBudget]
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    have h := ih (by omega)
    simp only [prefixBudget,Fin.val_castSucc,Fin.val_last]
    rw [←h]
    omega

lemma prefixBudget_full_le {n : ℕ} (p : Prepared n) :
    prefixBudget p n le_rfl≤∑k : Fin (n+1), levelBudget p k := by
  have h := prefixBudget_eq p n le_rfl
  simpa only [Fin.eta] using (Nat.le.intro h)

/-- The complete positive-depth control schedule has a linear fixed cost. -/
theorem prepare_prefixBudget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) :
    prefixBudget (prepare G rows hr hn) n le_rfl≤6*G.edgeFinset.card+17*n+4 :=
  (prefixBudget_full_le _).trans (levelBudget_sum G rows hr hn)

end HiddenCircuits.DH.LayerExecution
