import HiddenCircuits.DH.ComponentForestCorrectness

/-! A counted linear indexing pass converts component pairs to direct root
buckets and a root list. Member lists are shared, not rescanned or recopied. -/
namespace HiddenCircuits.DH.ComponentForest
open SimpleGraph

lemma roots_nodup_of_members {n : ℕ} (cs : List (Fin n × List (Fin n)))
    (hn : (cs.flatMap Prod.snd).Nodup) (hr : ∀c∈cs, c.1∈c.2) : (cs.map Prod.fst).Nodup := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    obtain ⟨hc,ht,hd⟩ := List.nodup_append.mp (show (c.2++cs.flatMap Prod.snd).Nodup from hn)
    apply List.nodup_cons.mpr
    refine ⟨?_,ih ht (fun d hd => hr d (List.mem_cons_of_mem _ hd))⟩
    intro hm
    obtain ⟨d,hd',he⟩ := List.mem_map.mp hm
    have htail : c.1∈cs.flatMap Prod.snd :=
      List.mem_flatMap.mpr ⟨d,hd',by rw [←he];exact hr d (List.mem_cons_of_mem _ hd')⟩
    exact hd c.1 (hr c List.mem_cons_self) c.1 htail rfl

lemma forest_roots_nodup {n : ℕ} {G : SimpleGraph (Fin n)} (rows : Vector (List (Fin n)) n)
    (hr : LinearBuckets.Adjacency.Represents G rows) : ((forest rows).components.map Prod.fst).Nodup := by
  apply roots_nodup_of_members _ (forest_nodup rows hr)
  intro c hc
  exact ((forest_components rows hr c hc).2.1 c.1).mpr (Reachable.refl _)

structure Index (n : ℕ) where
  buckets : Vector (List (Fin n)) n
  roots : List (Fin n)
  accesses : ℕ
  allocations : ℕ

def indexFrom {n : ℕ} : List (Fin n × List (Fin n)) → Vector (List (Fin n)) n → Index n
  | [],buckets => ⟨buckets,[],1,0⟩
  | (r,vs)::cs,buckets =>
      let q := indexFrom cs (buckets.set r.val vs)
      ⟨q.buckets,r::q.roots,q.accesses+3,q.allocations+1⟩

lemma indexFrom_roots {n : ℕ} (cs : List (Fin n × List (Fin n))) (buckets : Vector (List (Fin n)) n) :
    (indexFrom cs buckets).roots=cs.map Prod.fst := by
  induction cs generalizing buckets with
  | nil => rfl
  | cons c cs ih => simp [indexFrom,ih]
lemma indexFrom_accesses {n : ℕ} (cs : List (Fin n × List (Fin n))) (buckets : Vector (List (Fin n)) n) :
    (indexFrom cs buckets).accesses=3*cs.length+1 := by
  induction cs generalizing buckets with
  | nil => rfl
  | cons c cs ih => simp [indexFrom,ih];omega
lemma indexFrom_allocations {n : ℕ} (cs : List (Fin n × List (Fin n))) (buckets : Vector (List (Fin n)) n) :
    (indexFrom cs buckets).allocations=cs.length := by
  induction cs generalizing buckets with
  | nil => rfl
  | cons c cs ih => simp [indexFrom,ih]

lemma indexFrom_off {n : ℕ} (cs : List (Fin n × List (Fin n))) (buckets : Vector (List (Fin n)) n)
    (v : Fin n) (hv : v∉cs.map Prod.fst) : (indexFrom cs buckets).buckets[v.val]=buckets[v.val] := by
  induction cs generalizing buckets with
  | nil => rfl
  | cons c cs ih =>
    have hv' : v∉cs.map Prod.fst := by simp_all
    have hne : c.1.val≠v.val := by intro he;apply hv;exact List.mem_cons.mpr (Or.inl (Fin.ext he.symm))
    simpa [indexFrom,hne] using ih (buckets.set c.1.val c.2) hv'

lemma indexFrom_mem {n : ℕ} (cs : List (Fin n × List (Fin n))) (buckets : Vector (List (Fin n)) n)
    (hn : (cs.map Prod.fst).Nodup) (c : Fin n × List (Fin n)) (hc : c∈cs) :
    (indexFrom cs buckets).buckets[c.1.val]=c.2 := by
  induction cs generalizing buckets with
  | nil => simp at hc
  | cons b bs ih =>
    obtain ⟨hb,hbs⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hc with rfl | hc
    · simpa [indexFrom] using indexFrom_off bs (buckets.set c.1.val c.2) c.1 hb
    · simpa [indexFrom] using ih (buckets.set b.1.val b.2) hbs hc

structure IndexedOutput (n : ℕ) where
  owners : Vector (Fin n) n
  depths : Vector (Fin (n+1)) n
  roots : List (Fin n)
  buckets : Vector (List (Fin n)) n
  accesses : ℕ
  allocations : ℕ

def indexed {n : ℕ} (rows : Vector (List (Fin n)) n) : IndexedOutput n :=
  let q := build rows
  let b := indexFrom q.components (Vector.replicate n [])
  ⟨q.owners,q.depths,b.roots,b.buckets,q.accesses+b.accesses+n+2,q.allocations+b.allocations+n⟩

lemma indexed_roots_nodup {n : ℕ} {G : SimpleGraph (Fin n)} (rows : Vector (List (Fin n)) n)
    (hr : LinearBuckets.Adjacency.Represents G rows) : (indexed rows).roots.Nodup := by
  simpa only [indexed,indexFrom_roots,build] using forest_roots_nodup rows hr

lemma indexed_bucket {n : ℕ} {G : SimpleGraph (Fin n)} (rows : Vector (List (Fin n)) n)
    (hr : LinearBuckets.Adjacency.Represents G rows) (r : Fin n) (hr' : r∈(indexed rows).roots) :
    ((indexed rows).buckets[r.val]).Nodup ∧
      (∀v, v∈(indexed rows).buckets[r.val] ↔ G.Reachable r v) := by
  change r∈(indexFrom (forest rows).components (Vector.replicate n [])).roots at hr'
  rw [indexFrom_roots] at hr'
  obtain ⟨c,hc,he⟩ := List.mem_map.mp hr'
  subst r
  have hb := indexFrom_mem (forest rows).components (Vector.replicate n []) (forest_roots_nodup rows hr) c hc
  change ((indexFrom (forest rows).components (Vector.replicate n [])).buckets[c.1.val]).Nodup ∧
    (∀v, v∈(indexFrom (forest rows).components (Vector.replicate n [])).buckets[c.1.val] ↔ G.Reachable c.1 v)
  rw [hb]
  exact ⟨(forest_components rows hr c hc).1,(forest_components rows hr c hc).2.1⟩

lemma indexed_bucket_empty {n : ℕ} (rows : Vector (List (Fin n)) n) (r : Fin n)
    (hr : r∉(indexed rows).roots) : (indexed rows).buckets[r.val]=[] := by
  change r∉(indexFrom (forest rows).components (Vector.replicate n [])).roots at hr
  rw [indexFrom_roots] at hr
  simpa [indexed,build] using indexFrom_off (forest rows).components (Vector.replicate n []) r hr

lemma indexed_owner_bucket {n : ℕ} {G : SimpleGraph (Fin n)} (rows : Vector (List (Fin n)) n)
    (hr : LinearBuckets.Adjacency.Represents G rows) (v : Fin n) :
    (indexed rows).owners[v.val]∈(indexed rows).roots ∧
      v∈(indexed rows).buckets[((indexed rows).owners[v.val]).val] := by
  have hm := forest_members rows hr v
  obtain ⟨c,hc,hv⟩ := List.mem_flatMap.mp hm
  have ho := (forest_components rows hr c hc).2.2 v hv
  change (forest rows).owners[v.val]∈(indexed rows).roots ∧ _
  rw [ho]
  have hroot : c.1∈(indexed rows).roots := by
    change c.1∈(indexFrom (forest rows).components (Vector.replicate n [])).roots
    rw [indexFrom_roots]
    exact List.mem_map.mpr ⟨c,hc,rfl⟩
  refine ⟨hroot,?_⟩
  change v∈(indexed rows).buckets[((forest rows).owners[v.val]).val]
  have hvb := ((indexed_bucket rows hr c.1 hroot).2 v).mpr (((forest_components rows hr c hc).2.1 v).mp hv)
  have he := congrArg (fun r : Fin n => v∈(indexed rows).buckets[r.val]) ho
  exact he.mpr hvb

lemma indexed_resources {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : LinearBuckets.Adjacency.Represents G rows)
    (hn : ∀v : Fin n, (rows[v.val]).Nodup) :
    (indexed rows).accesses ≤ 14*G.edgeFinset.card+22*n+7 ∧
      (indexed rows).allocations ≤ 14*G.edgeFinset.card+22*n+7 := by
  have hbuild := build_spec G rows hr hn
  have hlen : (forest rows).components.length≤n := by
    have h := (forest_roots_nodup rows hr).length_le_card
    simpa only [List.length_map,Fintype.card_fin] using h
  have hacc := indexFrom_accesses (forest rows).components (Vector.replicate n [])
  have halloc := indexFrom_allocations (forest rows).components (Vector.replicate n [])
  change (build rows).accesses + (indexFrom (forest rows).components (Vector.replicate n [])).accesses+n+2≤_ ∧
    (build rows).allocations + (indexFrom (forest rows).components (Vector.replicate n [])).allocations+n≤_
  rw [hacc,halloc]
  constructor <;> omega

end HiddenCircuits.DH.ComponentForest
