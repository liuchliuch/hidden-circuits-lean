import HiddenCircuits.DH.LayerExecution
import HiddenCircuits.DH.LivePotential

/-! Actual one-step resource contracts for the static BFS-layer program. -/
namespace HiddenCircuits.DH.LayerExecution
open SimpleGraph LexBFSPartition LinearBuckets BlockCollapse

/-- Component-list scanning and branch dispatch are the only costs not paid by
permanently deleted original rows. -/
theorem componentStep_charge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) (p : LayerInput.Prepared n)
    (hscore : ∀v : Fin n, p.degree[v.val]=rows[v.val].length)
    (root : Fin n) (s : Working n) (I : ModuleExecution.Interpretation G s.store)
    (hmodule : (filterLive s.store p.components[root.val]).value≠[] →
      GraphModule (ModuleExecution.liveGraph G s.store)
        (ModuleExecution.liveModule s.store (filterLive s.store p.components[root.val]).value : Set (ModuleExecution.Live s.store)))
    (hfree : (filterLive s.store p.components[root.val]).value≠[] →
      P4Free ((ModuleExecution.liveGraph G s.store).induce
        (ModuleExecution.liveModule s.store (filterLive s.store p.components[root.val]).value : Set (ModuleExecution.Live s.store)))) :
    ∃out, (componentStep G rows hr hn p root s).value=some out ∧
      Nonempty (ModuleExecution.Interpretation G out.store) ∧
      (componentStep G rows hr hn p root s).accesses+1000*livePotential p.degree out.store.alive ≤
        1000*livePotential p.degree s.store.alive+3*(p.components[root.val]).length+4 := by
  let live := filterLive s.store p.components[root.val]
  have hf := filterLive_accesses s.store p.components[root.val]
  change live.accesses≤_ at hf
  by_cases he : (filterLive s.store p.components[root.val]).value=[]
  · refine ⟨s,?_,⟨I⟩,?_⟩
    · simp only [componentStep,he,↓reduceDIte]
    · simp only [componentStep,he,↓reduceDIte]
      dsimp only [live] at hf
      omega
  · obtain ⟨out,ho,hi,hk,ha,hcost⟩ := contractList_charge G rows hr hn p.degree hscore live.value
      (filterLive_nodup s.store _ (p.component_nodup root)) he s I
      (filterLive_live s.store _) (hmodule he) (hfree he)
    dsimp only [live] at ho
    refine ⟨out.state,?_,hi,?_⟩
    · simp only [componentStep,he,↓reduceDIte,ho,Option.map_some]
    · simp only [componentStep,he,↓reduceDIte]
      change live.accesses+(contractList G rows hr hn p.degree live.value _ s).accesses+3+
        1000*livePotential p.degree out.state.store.alive≤_
      omega

/-- Current predecessor-list scanning is charged once to its scheduled vertex.
The module and pendant work spend the decreasing original-row potential. -/
theorem vertexStep_charge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) (p : LayerInput.Prepared n)
    (hscore : ∀v : Fin n, p.degree[v.val]=rows[v.val].length)
    (v : Fin n) (s : Working n) (I : ModuleExecution.Interpretation G s.store)
    (hnot : v∉p.previous[v.val])
    (hne : s.store.alive[v.val]=true → (filterLive s.store p.previous[v.val]).value≠[])
    (hmodule : s.store.alive[v.val]=true → GraphModule (ModuleExecution.liveGraph G s.store)
      (ModuleExecution.liveModule s.store (filterLive s.store p.previous[v.val]).value : Set (ModuleExecution.Live s.store)))
    (hfree : s.store.alive[v.val]=true → P4Free ((ModuleExecution.liveGraph G s.store).induce
      (ModuleExecution.liveModule s.store (filterLive s.store p.previous[v.val]).value : Set (ModuleExecution.Live s.store)))) :
    ∃out, (vertexStep G rows hr hn p v s).value=some out ∧
      (vertexStep G rows hr hn p v s).accesses+1000*livePotential p.degree out.store.alive ≤
        1000*livePotential p.degree s.store.alive+3*(p.previous[v.val]).length+4 := by
  by_cases hv : s.store.alive[v.val]=true
  · let live := filterLive s.store p.previous[v.val]
    obtain ⟨out,ho,hi,hk,ha,hcost⟩ := contractList_charge G rows hr hn p.degree hscore live.value
      (filterLive_nodup s.store _ (p.previous_nodup v)) (hne hv) s I
      (filterLive_live s.store _) (hmodule hv) (hfree hv)
    have hv' : out.state.store.alive[v.val]=true := (ha v).mpr ⟨hv,Or.inr (by
      intro hm
      exact hnot (List.mem_filter.mp (filterLive_value s.store _ ▸ hm)).1)⟩
    have hp := absorb_charge p.degree out.state.store out.kept v hv'
    have hf := filterLive_accesses s.store p.previous[v.val]
    change live.accesses≤_ at hf
    dsimp only [live] at ho
    refine ⟨(absorbWorking out.state out.kept v).value,?_,?_⟩
    · simp only [vertexStep,if_pos hv,ho]
    · simp only [vertexStep,if_pos hv,ho,absorbWorking]
      change live.accesses+(contractList G rows hr hn p.degree live.value _ s).accesses+
        (ModuleExecution.absorb out.state.store out.kept v).accesses+3+
        1000*livePotential p.degree (ModuleExecution.absorb out.state.store out.kept v).value.alive≤_
      omega
  · refine ⟨s,?_,?_⟩
    · simp only [vertexStep,if_neg hv]
    · simp only [vertexStep,if_neg hv]
      omega

/-- List-loop composition with a changing semantic invariant. Every local
contract is about the literal step result; no work is replaced by an oracle. -/
theorem runSteps_potential {n : ℕ}
    (step : Fin n→Working n→Counted (Option (Working n))) (scores : Vector ℕ n)
    (budget : Fin n→ℕ) (Inv : List (Fin n)→Working n→Prop)
    (xs : List (Fin n)) (s : Working n) (hI : Inv xs s)
    (hstep : ∀v vs t, Inv (v::vs) t → ∃out, (step v t).value=some out ∧ Inv vs out ∧
      (step v t).accesses+1000*livePotential scores out.store.alive ≤
        1000*livePotential scores t.store.alive+budget v) :
    ∃out, (runSteps step xs s).value=some out ∧ Inv [] out ∧
      (runSteps step xs s).accesses+1000*livePotential scores out.store.alive ≤
        1000*livePotential scores s.store.alive+(xs.map (fun v=>budget v+1)).sum := by
  induction xs generalizing s with
  | nil => exact ⟨s,rfl,hI,by simp [runSteps]⟩
  | cons v vs ih =>
    obtain ⟨next,he,hi,hc⟩ := hstep v vs s hI
    obtain ⟨out,ho,hio,hco⟩ := ih next hi
    refine ⟨out,?_,hio,?_⟩
    · simp only [runSteps,he,ho]
    · simp only [runSteps,he,List.map_cons,List.sum_cons]
      omega

end HiddenCircuits.DH.LayerExecution
