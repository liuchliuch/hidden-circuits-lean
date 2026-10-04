import HiddenCircuits.DH.LayerScheduleBudget

/-! Composition of the actual layer loops and the ordinary-input resource bound. -/
namespace HiddenCircuits.DH.LayerExecution
open SimpleGraph LexBFSPartition LinearBuckets BlockCollapse LayerInput

/-- The descending control loop composes proved semantic phase contracts.
The callback refers to the two actual runSteps results at the current level. -/
theorem runLevels_potential {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) (p : Prepared n)
    (Inv : ℕ→Working n→Prop)
    (hphase : ∀k (hk : k+1≤n) s, Inv (k+1) s →
      ∃mid out,
        (runSteps (componentStep G rows hr hn p) p.componentByLevel[k+1] s).value=some mid ∧
        (runSteps (vertexStep G rows hr hn p) p.vertexByLevel[k+1] mid).value=some out ∧
        Inv k out ∧
        (runSteps (componentStep G rows hr hn p) p.componentByLevel[k+1] s).accesses+
          (runSteps (vertexStep G rows hr hn p) p.vertexByLevel[k+1] mid).accesses+
          1000*livePotential p.degree out.store.alive ≤
            1000*livePotential p.degree s.store.alive+
              componentBudget p ⟨k+1,by omega⟩+vertexBudget p ⟨k+1,by omega⟩)
    (fuel : ℕ) (hf : fuel≤n) (s : Working n) (hI : Inv fuel s) :
    ∃out, (runLevels G rows hr hn p fuel hf s).value=some out ∧ Inv 0 out ∧
      (runLevels G rows hr hn p fuel hf s).accesses+1000*livePotential p.degree out.store.alive ≤
        1000*livePotential p.degree s.store.alive+prefixBudget p fuel hf := by
  induction fuel generalizing s with
  | zero => exact ⟨s,rfl,hI,by simp [runLevels,prefixBudget]⟩
  | succ k ih =>
    obtain ⟨mid,next,hm,hn',hnext,hcost⟩ := hphase k hf s hI
    obtain ⟨out,ho,hi,hrest⟩ := ih (by omega) next hnext
    refine ⟨out,?_,hi,?_⟩
    · simp only [runLevels,hm,hn',ho]
    · simp only [runLevels,hm,hn',prefixBudget,levelBudget]
      omega

/-- Once the actual layer loop has its proved potential contract, all input
construction and initialization costs are included by this ordinary-input bound. -/
theorem run_accesses_of_potential {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) (out : Working n)
    (hcost : (runLevels G rows hr hn (prepare G rows hr hn) n le_rfl (initial n).value).accesses+
      1000*livePotential (prepare G rows hr hn).degree out.store.alive ≤
      1000*livePotential (prepare G rows hr hn).degree (initial n).value.store.alive+
        prefixBudget (prepare G rows hr hn) n le_rfl) :
    (run G rows hr hn).accesses≤2060*G.edgeFinset.card+1105*n+21 := by
  have hp := LayerInput.prepare_accesses G rows hr hn
  have hb := prepare_prefixBudget G rows hr hn
  have hi := initial_potential G rows hr hn (prepare G rows hr hn).degree
    (prepare_degree G rows hr hn)
  change livePotential (prepare G rows hr hn).degree (initial n).value.store.alive=_ at hi
  have hinit := initial_accesses n
  change (prepare G rows hr hn).accesses+(initial n).accesses+
    (runLevels G rows hr hn (prepare G rows hr hn) n le_rfl (initial n).value).accesses≤_
  omega

lemma decompose_accesses_of_run {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) (out : Working n)
    (ho : (run G rows hr hn).value=some out)
    (hc : (run G rows hr hn).accesses≤2060*G.edgeFinset.card+1105*n+21) :
    (decompose G rows hr hn).value=some (ModuleExecution.finish out.store).value ∧
      (decompose G rows hr hn).accesses≤2060*G.edgeFinset.card+1115*n+22 := by
  have hf := ModuleExecution.finish_accesses out.store
  simp only [decompose,ho]
  constructor
  · trivial
  · omega

end HiddenCircuits.DH.LayerExecution
