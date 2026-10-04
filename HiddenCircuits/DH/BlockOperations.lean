import HiddenCircuits.DH.BlockCollapse
import HiddenCircuits.DH.PendantExecution

/-! Counted live-list filtering and the empty/singleton cases of block contraction.
Singletons never trigger an induced-row scan or cotree construction. -/
namespace HiddenCircuits.DH.BlockCollapse
open SimpleGraph LexBFSPartition LinearBuckets

/-- Scan only the supplied static list; no global live-set traversal occurs. -/
def filterLive {n : ℕ} (s : ModuleExecution.Store n) : List (Fin n) → Counted (List (Fin n))
  | [] => ⟨[],0⟩
  | v::vs =>
      let q := filterLive s vs
      if s.alive[v.val] then ⟨v::q.value,q.accesses+3⟩ else ⟨q.value,q.accesses+2⟩

@[simp] theorem filterLive_value {n : ℕ} (s : ModuleExecution.Store n) (vs : List (Fin n)) :
    (filterLive s vs).value=vs.filter (fun v=>s.alive[v.val]) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => cases hv : s.alive[v.val] <;> simp [filterLive,hv,ih]

lemma filterLive_accesses {n : ℕ} (s : ModuleExecution.Store n) (vs : List (Fin n)) :
    (filterLive s vs).accesses≤3*vs.length := by
  induction vs with
  | nil => simp [filterLive]
  | cons v vs ih => cases hv : s.alive[v.val] <;> simp [filterLive,hv] <;> omega

lemma filterLive_nodup {n : ℕ} (s : ModuleExecution.Store n) (vs : List (Fin n)) (hn : vs.Nodup) :
    (filterLive s vs).value.Nodup := by rw [filterLive_value];exact hn.filter _

lemma filterLive_live {n : ℕ} (s : ModuleExecution.Store n) (vs : List (Fin n)) :
    ∀v∈(filterLive s vs).value, s.alive[v.val]=true := by
  intro v hv
  rw [filterLive_value] at hv
  exact (List.mem_filter.mp hv).2

/-- Empty lists fail; singleton blocks return immediately; only genuinely
nontrivial blocks invoke sparse induced extraction and cotree construction. -/
def contractList {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) (scores : Vector ℕ n)
    (vertices : List (Fin n)) (hs : vertices.Nodup) (s : Working n) : Counted (Option (Result n)) :=
  match vertices with
  | [] => ⟨none,1⟩
  | [a] => ⟨some ⟨s,a⟩,1⟩
  | a::b::rest => collapse G rows hr hn scores a b rest hs s

/-- The local compact vertex array embeds into the actual current block graph. -/
lemma local_p4Free {n : ℕ} (G : SimpleGraph (Fin n))
    (rows : Vector (List (Fin n)) n) (vertices : List (Fin n)) (hs : vertices.Nodup) (s : Working n)
    (hlive : ∀v∈vertices, s.store.alive[v.val]=true)
    (hfree : P4Free ((ModuleExecution.liveGraph G s.store).induce
      (ModuleExecution.liveModule s.store vertices : Set (ModuleExecution.Live s.store)))) :
    P4Free (G.comap (fun i : Fin vertices.length =>
      (InducedInput.prepare rows vertices s.epoch s.workspace).vertices[i.val])) := by
  let labels := (InducedInput.prepare rows vertices s.epoch s.workspace).vertices
  have hm (i : Fin vertices.length) : labels[i.val]∈vertices :=
    (InducedInput.prepare_image rows vertices s.epoch s.workspace _).mp ⟨i,rfl⟩
  apply hfree.of_embedding
  exact
    { toFun:=fun i=>⟨⟨labels[i.val],hlive _ (hm i)⟩,by simpa using hm i⟩
      inj':=by
        intro i j he
        apply InducedInput.prepare_injective rows vertices s.epoch s.workspace hs
        exact congrArg (fun v=>v.val.val) he
      map_rel_iff':=by intro i j;rfl }

/-- This executable wrapper has no supplied cograph certificate. Its semantic
side conditions establish success for every nonempty live cograph module. -/
theorem contractList_correct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) (scores : Vector ℕ n)
    (vertices : List (Fin n)) (hs : vertices.Nodup) (hne : vertices≠[]) (s : Working n)
    (I : ModuleExecution.Interpretation G s.store)
    (hlive : ∀v∈vertices, s.store.alive[v.val]=true)
    (hmodule : GraphModule (ModuleExecution.liveGraph G s.store)
      (ModuleExecution.liveModule s.store vertices : Set (ModuleExecution.Live s.store)))
    (hfree : P4Free ((ModuleExecution.liveGraph G s.store).induce
      (ModuleExecution.liveModule s.store vertices : Set (ModuleExecution.Live s.store)))) :
    ∃out, (contractList G rows hr hn scores vertices hs s).value=some out ∧
      Nonempty (ModuleExecution.Interpretation G out.state.store) ∧
      out.kept∈vertices ∧ (∀v∈vertices, scores[out.kept.val]≤scores[v.val]) ∧
      (∀v, out.state.store.alive[v.val]=true ↔
        s.store.alive[v.val]=true ∧ (v=out.kept ∨ v∉vertices)) := by
  cases vertices with
  | nil => contradiction
  | cons a vertices =>
    cases vertices with
    | nil =>
      refine ⟨⟨s,a⟩,rfl,⟨I⟩,by simp,?_,?_⟩
      · intro v hv;simpa using le_of_eq (congrArg (fun x : Fin n=>scores[x.val]) (List.mem_singleton.mp hv).symm)
      · intro v; by_cases hv : v=a <;> simp [hv]
    | cons b rest =>
      obtain ⟨out,ho,hi,hk,hmin,ha,he⟩ := collapse_correct G rows hr hn scores a b rest hs s I hlive hmodule
        (local_p4Free G rows _ hs s hlive hfree)
      exact ⟨out,ho,hi,hk,hmin,ha⟩

/-- A constant singleton cost avoids rescanning a high-degree survivor when no
vertex would be deleted. The nontrivial branch is bounded by its actual rows. -/
theorem contractList_accesses {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) (scores : Vector ℕ n)
    (vertices : List (Fin n)) (hs : vertices.Nodup) (s : Working n)
    (hlive : ∀v∈vertices, s.store.alive[v.val]=true)
    (hfree : P4Free ((ModuleExecution.liveGraph G s.store).induce
      (ModuleExecution.liveModule s.store vertices : Set (ModuleExecution.Live s.store)))) :
    (contractList G rows hr hn scores vertices hs s).accesses ≤
      if vertices.length≤1 then 1 else
        500*(vertices.length+(vertices.map (fun v=>rows[v.val].length)).sum) := by
  cases vertices with
  | nil => simp [contractList]
  | cons a vertices =>
    cases vertices with
    | nil => simp [contractList]
    | cons b rest =>
      simpa only [contractList,List.length_cons,Nat.not_succ_le_self,show ¬rest.length+1+1≤1 by omega,↓reduceIte] using
        collapse_accesses G rows hr hn scores a b rest hs s (local_p4Free G rows _ hs s hlive hfree)

end HiddenCircuits.DH.BlockCollapse
