import HiddenCircuits.DH.InducedInput
import HiddenCircuits.DH.ExtractionCharge
import HiddenCircuits.DH.ModuleStoreSemantics
import HiddenCircuits.DH.CographFrontend

/-! The actual nontrivial cograph-block update: choose a survivor, extract local rows,
construct the cotree, restore labels, and update the fixed-size bag store. -/
namespace HiddenCircuits.DH.BlockCollapse
open SimpleGraph LexBFSPartition LinearBuckets

structure Working (n : ℕ) where
  store : ModuleExecution.Store n
  workspace : InducedInput.Workspace n
  epoch : ℕ
  ready : InducedInput.Ready workspace epoch

structure Result (n : ℕ) where
  state : Working n
  kept : Fin n

/-- All graph work is performed on the supplied original rows and the live block list.
The workspace freshness and input-list proofs are erased low-level safety obligations. -/
def collapse (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀ v : Fin n, rows[v.val].Nodup) (scores : Vector ℕ n)
    (a b : Fin n) (rest : List (Fin n)) (hs : (a::b::rest).Nodup) (s : Working n) :
    Counted (Option (Result n)) :=
  let vertices := a::b::rest
  let chosen := ExtractionCharge.chooseFrom scores a (b::rest)
  let input := InducedInput.prepare rows vertices s.epoch s.workspace
  let localGraph := G.comap (fun i : Fin vertices.length => input.vertices[i.val])
  let localRows := InducedInput.prepare_represents G rows hr vertices s.epoch s.workspace s.ready hs
  let localNodup := InducedInput.prepare_nodup rows hn vertices s.epoch s.workspace s.ready hs
  let cograph := CographFrontend.construct localGraph input.rows localRows localNodup
  match cograph.tree with
  | none => ⟨none,chosen.accesses+input.accesses+cograph.accesses+1⟩
  | some t =>
      let lifted := InducedInput.restoreTree input.vertices t
      let next := ModuleExecution.contract s.store vertices chosen.vertex lifted.value
      let out : Working n := ⟨next.value,input.workspace,s.epoch+1,
        InducedInput.prepare_ready rows vertices s.epoch s.workspace s.ready⟩
      ⟨some ⟨out,chosen.vertex⟩,
        chosen.accesses+input.accesses+cograph.accesses+lifted.accesses+next.accesses+3⟩

/-- The computed survivor belongs to the block and is minimum in the fixed original-degree array. -/
lemma chosen_spec {n : ℕ} (scores : Vector ℕ n) (a b : Fin n) (rest : List (Fin n)) :
    (ExtractionCharge.chooseFrom scores a (b::rest)).vertex∈a::b::rest ∧
      ∀ v∈a::b::rest, scores[(ExtractionCharge.chooseFrom scores a (b::rest)).vertex.val] ≤ scores[v.val] := by
  have h := ExtractionCharge.chooseFrom_spec scores a (b::rest)
  refine ⟨List.mem_cons.mpr h.1,?_⟩
  intro v hv
  rcases List.mem_cons.mp hv with rfl | hv
  · exact h.2.1
  · exact h.2.2 v hv

/-- No cotree or pruning certificate is supplied to the executable collapse.
Semantic cograph/module facts imply success and preserve the original graph interpretation. -/
theorem collapse_correct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀ v : Fin n, rows[v.val].Nodup) (scores : Vector ℕ n)
    (a b : Fin n) (rest : List (Fin n)) (hs : (a::b::rest).Nodup) (s : Working n)
    (I : ModuleExecution.Interpretation G s.store)
    (hlive : ∀ v∈a::b::rest, s.store.alive[v.val]=true)
    (hmodule : GraphModule (ModuleExecution.liveGraph G s.store)
      (ModuleExecution.liveModule s.store (a::b::rest) : Set (ModuleExecution.Live s.store)))
    (hfree : P4Free (G.comap (fun i : Fin (a::b::rest).length =>
      (InducedInput.prepare rows (a::b::rest) s.epoch s.workspace).vertices[i.val]))) :
    ∃ out, (collapse G rows hr hn scores a b rest hs s).value=some out ∧
      Nonempty (ModuleExecution.Interpretation G out.state.store) ∧
      out.kept∈a::b::rest ∧
      (∀ v∈a::b::rest, scores[out.kept.val] ≤ scores[v.val]) ∧
      (∀ v, out.state.store.alive[v.val]=true ↔
        s.store.alive[v.val]=true ∧ (v=out.kept ∨ v∉a::b::rest)) ∧
      out.state.epoch=s.epoch+1 := by
  let vertices := a::b::rest
  let chosen := ExtractionCharge.chooseFrom scores a (b::rest)
  let input := InducedInput.prepare rows vertices s.epoch s.workspace
  let localGraph := G.comap (fun i : Fin vertices.length => input.vertices[i.val])
  let localRows := InducedInput.prepare_represents G rows hr vertices s.epoch s.workspace s.ready hs
  let localNodup := InducedInput.prepare_nodup rows hn vertices s.epoch s.workspace s.ready hs
  obtain ⟨t,ht,htC,htN,htAll,_,_⟩ := CographFrontend.construct_spec localGraph hfree
    input.rows localRows localNodup (by simp [vertices])
  let lifted := InducedInput.restoreTree input.vertices t
  have hlift := InducedInput.restoreTree_spec G rows vertices s.epoch s.workspace hs t htN htC htAll
  have hchosen := chosen_spec scores a b rest
  let next := ModuleExecution.contract s.store vertices chosen.vertex lifted.value
  let outState : Working n := ⟨next.value,input.workspace,s.epoch+1,
    InducedInput.prepare_ready rows vertices s.epoch s.workspace s.ready⟩
  let out : Result n := ⟨outState,chosen.vertex⟩
  refine ⟨out,?_,?_,hchosen.1,hchosen.2,?_,rfl⟩
  · dsimp only [collapse]
    rw [ht]
  · exact ⟨I.contract vertices chosen.vertex hchosen.1 hlive lifted.value hlift.2.1 hlift.1 hlift.2.2 hmodule⟩
  · intro v
    exact ModuleExecution.contract_alive s.store vertices chosen.vertex lifted.value v

/-- Every stage of a successful nontrivial collapse is linear in the block and
its original adjacency rows, including both LexBFS sweeps and compact copying. -/
theorem collapse_accesses {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀ v : Fin n, rows[v.val].Nodup) (scores : Vector ℕ n)
    (a b : Fin n) (rest : List (Fin n)) (hs : (a::b::rest).Nodup) (s : Working n)
    (hfree : P4Free (G.comap (fun i : Fin (a::b::rest).length =>
      (InducedInput.prepare rows (a::b::rest) s.epoch s.workspace).vertices[i.val]))) :
    (collapse G rows hr hn scores a b rest hs s).accesses ≤
      500*((a::b::rest).length+((a::b::rest).map (fun v => rows[v.val].length)).sum) := by
  let vertices := a::b::rest
  let chosen := ExtractionCharge.chooseFrom scores a (b::rest)
  let input := InducedInput.prepare rows vertices s.epoch s.workspace
  let localGraph := G.comap (fun i : Fin vertices.length => input.vertices[i.val])
  let localRows := InducedInput.prepare_represents G rows hr vertices s.epoch s.workspace s.ready hs
  let localNodup := InducedInput.prepare_nodup rows hn vertices s.epoch s.workspace s.ready hs
  obtain ⟨t,ht,_,htN,htAll,hcost,_⟩ := CographFrontend.construct_spec localGraph hfree
    input.rows localRows localNodup (by simp [vertices])
  have hlen : t.leaves.length=vertices.length := by
    have hp : t.leaves.Perm (List.finRange vertices.length) :=
      (List.perm_ext_iff_of_nodup htN (List.nodup_finRange _)).mpr
        (by intro v; simp [htAll v])
    simpa using hp.length_eq
  have hnodes := t.shape.nodes_eq
  rw [LabeledCographTree.shape_leaves,hlen] at hnodes
  have hchoose := ExtractionCharge.chooseFrom_accesses scores a (b::rest)
  have hprep := InducedInput.prepare_accesses rows vertices s.epoch s.workspace
  have hinc := InducedInput.prepare_incidence_le rows vertices s.epoch s.workspace
  have hrestore := InducedInput.restoreTree_accesses input.vertices t
  have hcontract := ModuleExecution.contract_accesses s.store vertices chosen.vertex
    (InducedInput.restoreTree input.vertices t).value
  simp only [InducedInput.restoreTree_value,LabeledCographTree.mapLabels_shape] at hcontract
  dsimp only [collapse]
  rw [ht]
  change chosen.accesses+input.accesses+
    (CographFrontend.construct localGraph input.rows localRows localNodup).accesses+
    (InducedInput.restoreTree input.vertices t).accesses+
    (ModuleExecution.contract s.store vertices chosen.vertex
      (InducedInput.restoreTree input.vertices t).value).accesses+3 ≤
      500*(vertices.length+(vertices.map (fun v => rows[v.val].length)).sum)
  change chosen.accesses=4*(b::rest).length at hchoose
  change input.accesses≤_ at hprep
  change Adjacency.incidenceCount input.rows≤_ at hinc
  have hv : vertices.length=rest.length+2 := by simp [vertices]
  simp only [List.length_cons] at hchoose
  simp only [InducedInput.restoreTree_value]
  omega

end HiddenCircuits.DH.BlockCollapse
