import HiddenCircuits.DH.LayerExecutionCorrectness

/-! Ordinary-input graph preprocessing and the actual integer matching evaluator.
Graph-processing resources count the explicit sparse array/list operations;
numeric resources count integer coefficient arithmetic, with bit magnitudes
proved for every observed temporary in the same execution. -/
namespace HiddenCircuits.DH.LinearPreprocessing
open SimpleGraph LexBFSPartition LinearBuckets BlockCollapse

/-- Empty input returns immediately without allocating any graph arrays. All
nonempty input uses the actual static BFS-layer elimination program. -/
def preprocess {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) : Counted (Option (List BagExpr)) :=
  if n=0 then ⟨some [],0⟩ else LayerExecution.decompose G rows hr hn

structure Result where
  value : Option ℤ
  preprocessing : ℕ
  arithmetic : ℕ

/-- This program computes preprocessing internally and evaluates only the
resulting bag recurrences; it never enumerates matchings. -/
def count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) : Result :=
  let p := preprocess G rows hr hn
  match p.value with
  | none => ⟨none,p.accesses,0⟩
  | some es =>
      let q := BagForest.execute es
      ⟨some q.value,p.accesses,q.operations⟩

def emptyIso (G : SimpleGraph (Fin 0)) : BagForest.graph [] ≃g G where
  toEquiv :=
    { toFun:=Empty.elim
      invFun:=Fin.elim0
      left_inv:=by intro a;cases a
      right_inv:=by intro a;exact Fin.elim0 a }
  map_rel_iff' := by intro a;cases a

/-- Refinement bridge from a proved actual layer-run result. The ordinary DH
endpoint discharges these hypotheses from graph semantics, rather than taking
a decomposition or pruning certificate as input. -/
theorem preprocess_spec_of_run {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) (out : Working n)
    (ho : (LayerExecution.run G rows hr hn).value=some out)
    (I : ModuleExecution.Interpretation G out.store)
    (hedge : ∀a b : ModuleExecution.Live out.store, ¬(ModuleExecution.liveGraph G out.store).Adj a b)
    (hc : (LayerExecution.run G rows hr hn).accesses≤2060*G.edgeFinset.card+1105*n+21) :
    ∃es, (preprocess G rows hr hn).value=some es ∧ Nonempty (BagForest.graph es ≃g G) ∧
      (preprocess G rows hr hn).accesses≤2200*(n+G.edgeFinset.card) := by
  by_cases hz : n=0
  · subst n
    exact ⟨[],by simp [preprocess],⟨emptyIso G⟩,by simp [preprocess]⟩
  · obtain ⟨he,hcost⟩ := LayerExecution.decompose_accesses_of_run G rows hr hn out ho hc
    refine ⟨(ModuleExecution.finish out.store).value,?_,⟨I.finishIso hedge⟩,?_⟩
    · simpa only [preprocess,if_neg hz] using he
    · simp only [preprocess,if_neg hz]
      omega

/-- Matching correctness and all numeric temporary bit bounds are inherited
by the very forest actually returned by ordinary-input preprocessing. -/
theorem count_spec_of_preprocess {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) (es : List BagExpr)
    (he : (preprocess G rows hr hn).value=some es) (iso : BagForest.graph es ≃g G)
    (hc : (preprocess G rows hr hn).accesses≤2200*(n+G.edgeFinset.card)) :
    (count G rows hr hn).value=some (perfectMatchingCount G : ℤ) ∧
      (count G rows hr hn).preprocessing≤2200*(n+G.edgeFinset.card) ∧
      (count G rows hr hn).arithmetic≤36*n.choose 2+n ∧
      ExecutionBits.ForestProperty (fun z=>z.natAbs.size≤(3*n+3)*(n+1).size+2) es := by
  have h := ExecutionBits.complete_execution_bit_spec_of_iso es G iso
  simp only [Fintype.card_fin] at h
  simp only [count,he]
  exact ⟨congrArg some h.1,hc,h.2.1,h.2.2⟩

/-- Genuine linear graph preprocessing from ordinary distance-hereditary input.
The only graph-class assumption is the metric, induced-distance definition. -/
theorem preprocess_spec {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : DistanceHereditaryGraph G) (rows : Vector (List (Fin n)) n)
    (hr : Adjacency.Represents G rows) (hn : ∀v : Fin n, rows[v.val].Nodup) :
    ∃es, (preprocess G rows hr hn).value=some es ∧ Nonempty (BagForest.graph es ≃g G) ∧
      (preprocess G rows hr hn).accesses≤2200*(n+G.edgeFinset.card) := by
  obtain ⟨out,ho,hg,hb,he,hc⟩ := LayerExecution.run_correct G rows hr hn hG
  obtain ⟨I⟩ := hg.interpretation
  exact preprocess_spec_of_run G rows hr hn out ho I he hc

/-- Section 12's full ordinary-input counting algorithm: actual linear sparse
preprocessing, quadratic integer arithmetic, and bounded magnitude bits for
every intermediate of the returned forest's actual numerical execution. -/
theorem count_spec {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : DistanceHereditaryGraph G) (rows : Vector (List (Fin n)) n)
    (hr : Adjacency.Represents G rows) (hn : ∀v : Fin n, rows[v.val].Nodup) :
    ∃es, (preprocess G rows hr hn).value=some es ∧
      (count G rows hr hn).value=some (perfectMatchingCount G : ℤ) ∧
      (count G rows hr hn).preprocessing≤2200*(n+G.edgeFinset.card) ∧
      (count G rows hr hn).arithmetic≤36*n.choose 2+n ∧
      ExecutionBits.ForestProperty (fun z=>z.natAbs.size≤(3*n+3)*(n+1).size+2) es := by
  obtain ⟨es,he,⟨iso⟩,hc⟩ := preprocess_spec G hG rows hr hn
  exact ⟨es,he,count_spec_of_preprocess G rows hr hn es he iso hc⟩

/-- The same ordinary-input program applies to quasi-chain graphs by the proved
semantic graph-class inclusion; no quasi-chain ordering is supplied. -/
theorem quasiChains_count_spec {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : QuasiChains G) (rows : Vector (List (Fin n)) n)
    (hr : Adjacency.Represents G rows) (hn : ∀v : Fin n, rows[v.val].Nodup) :
    ∃es, (preprocess G rows hr hn).value=some es ∧
      (count G rows hr hn).value=some (perfectMatchingCount G : ℤ) ∧
      (count G rows hr hn).preprocessing≤2200*(n+G.edgeFinset.card) ∧
      (count G rows hr hn).arithmetic≤36*n.choose 2+n ∧
      ExecutionBits.ForestProperty (fun z=>z.natAbs.size≤(3*n+3)*(n+1).size+2) es :=
  count_spec G (quasiChains_distanceHereditary hG) rows hr hn

@[simp] theorem count_empty (G : SimpleGraph (Fin 0)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin 0)) 0) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin 0, rows[v.val].Nodup) :
    (count G rows hr hn).value=some 1 ∧ (count G rows hr hn).preprocessing=0 ∧
      (count G rows hr hn).arithmetic=0 := by
  simp [count,preprocess,BagForest.execute]

end HiddenCircuits.DH.LinearPreprocessing
