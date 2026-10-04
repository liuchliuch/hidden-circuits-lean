import HiddenCircuits.DH.LayerInput
import HiddenCircuits.DH.BlockOperations
import HiddenCircuits.DH.StoreFinalization

/-! The actual static BFS-layer elimination program. Its loops read only the
computed layer arrays, live marks, and relevant original adjacency rows. -/
namespace HiddenCircuits.DH.LayerExecution
open SimpleGraph LexBFSPartition LinearBuckets BlockCollapse

/-- Retain the extraction workspace when performing the constant-time pendant update. -/
def absorbWorking {n : ℕ} (s : Working n) (keep removed : Fin n) : Counted (Working n) :=
  let q := ModuleExecution.absorb s.store keep removed
  ⟨⟨q.value,s.workspace,s.epoch,s.ready⟩,q.accesses⟩

/-- Collapse the currently surviving members of one original same-depth component.
An empty component needs no work, and contractList skips singleton extraction. -/
def componentStep {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) (p : LayerInput.Prepared n)
    (root : Fin n) (s : Working n) : Counted (Option (Working n)) :=
  let live := filterLive s.store p.components[root.val]
  if he : live.value=[] then ⟨some s,live.accesses+2⟩ else
    let q := contractList G rows hr hn p.degree live.value
      (filterLive_nodup s.store _ (p.component_nodup root)) s
    ⟨q.value.map Result.state,live.accesses+q.accesses+3⟩

/-- A positive-layer vertex first merges its current predecessors and then is
absorbed as a pendant. A missing predecessor or failed cotree returns failure. -/
def vertexStep {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) (p : LayerInput.Prepared n)
    (v : Fin n) (s : Working n) : Counted (Option (Working n)) :=
  if s.store.alive[v.val] then
    let live := filterLive s.store p.previous[v.val]
    let q := contractList G rows hr hn p.degree live.value
      (filterLive_nodup s.store _ (p.previous_nodup v)) s
    match q.value with
    | none => ⟨none,live.accesses+q.accesses+3⟩
    | some out =>
        let next := absorbWorking out.state out.kept v
        ⟨some next.value,live.accesses+q.accesses+next.accesses+3⟩
  else ⟨some s,2⟩

/-- Structural list loop, with no repeated list-length computations. -/
def runSteps {n : ℕ} (step : Fin n→Working n→Counted (Option (Working n))) :
    List (Fin n)→Working n→Counted (Option (Working n))
  | [],s => ⟨some s,0⟩
  | v::vs,s =>
      let q := step v s
      match q.value with
      | none => ⟨none,q.accesses+1⟩
      | some next =>
          let rest := runSteps step vs next
          ⟨rest.value,q.accesses+rest.accesses+1⟩

/-- Process positive depths from n down through one. The depth-zero component
roots are deliberately retained for the final disjoint union. -/
def runLevels {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) (p : LayerInput.Prepared n) :
    (fuel : ℕ)→fuel≤n→Working n→Counted (Option (Working n))
  | 0,_,s => ⟨some s,0⟩
  | k+1,hk,s =>
      let level : Fin (n+1) := ⟨k+1,by omega⟩
      let a := runSteps (componentStep G rows hr hn p) p.componentByLevel[level.val] s
      match a.value with
      | none => ⟨none,a.accesses+3⟩
      | some afterComponents =>
          let b := runSteps (vertexStep G rows hr hn p) p.vertexByLevel[level.val] afterComponents
          match b.value with
          | none => ⟨none,a.accesses+b.accesses+4⟩
          | some afterVertices =>
              let q := runLevels G rows hr hn p k (by omega) afterVertices
              ⟨q.value,a.accesses+b.accesses+q.accesses+4⟩

def initial (n : ℕ) : Counted (Working n) :=
  let w := InducedInput.initial n
  ⟨⟨ModuleExecution.initial n,w.value,1,InducedInput.initial_ready n⟩,w.accesses+2*n⟩

/-- Ordinary-input preprocessing: all component, layer, predecessor and ordering
arrays are computed internally; the input contains no pruning certificate. -/
def run {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) : Counted (Option (Working n)) :=
  let p := LayerInput.prepare G rows hr hn
  let s := initial n
  let q := runLevels G rows hr hn p n le_rfl s.value
  ⟨q.value,p.accesses+s.accesses+q.accesses⟩

/-- The final expression forest is materialized from the surviving root bags. -/
def decompose {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) : Counted (Option (List BagExpr)) :=
  let q := run G rows hr hn
  match q.value with
  | none => ⟨none,q.accesses+1⟩
  | some s =>
      let out := ModuleExecution.finish s.store
      ⟨some out.value,q.accesses+out.accesses+1⟩

@[simp] lemma initial_accesses (n : ℕ) : (initial n).accesses=4*n := by
  simp [initial,InducedInput.initial];omega

lemma initial_interpretation (G : SimpleGraph (Fin n)) :
    Nonempty (ModuleExecution.Interpretation G (initial n).value.store) :=
  ⟨ModuleExecution.initialInterpretation G⟩

end HiddenCircuits.DH.LayerExecution
