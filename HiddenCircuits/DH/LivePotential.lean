import HiddenCircuits.DH.BlockOperations

/-! A decreasing original-row potential pays for every successful module call.
The potential is proof-only; the executable algorithm never sums it. -/
namespace HiddenCircuits.DH.BlockCollapse
open SimpleGraph LexBFSPartition LinearBuckets
open scoped BigOperators

/-- Each remaining representative owns its original row plus one vertex unit. -/
def livePotential {n : ℕ} (scores : Vector ℕ n) (alive : Vector Bool n) : ℕ :=
  ∑v∈Finset.univ.filter (fun v : Fin n=>alive[v.val]=true), (scores[v.val]+1)

lemma mask_potential {n : ℕ} (scores : Vector ℕ n) (alive next : Vector Bool n)
    (vertices : List (Fin n)) (keep : Fin n)
    (hlive : ∀v∈vertices, alive[v.val]=true)
    (hnext : ∀v, next[v.val]=true ↔ alive[v.val]=true ∧ (v=keep ∨ v∉vertices)) :
    livePotential scores next +
      (∑v∈vertices.toFinset.erase keep, (scores[v.val]+1)) = livePotential scores alive := by
  let old := Finset.univ.filter (fun v : Fin n=>alive[v.val]=true)
  let gone := vertices.toFinset.erase keep
  have hsub : gone⊆old := by
    intro v hv
    have hm := Finset.mem_of_mem_erase hv
    simp only [old,Finset.mem_filter,Finset.mem_univ,true_and]
    exact hlive v (List.mem_toFinset.mp hm)
  have he : Finset.univ.filter (fun v : Fin n=>next[v.val]=true) = old\gone := by
    ext v
    simp only [old,gone,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff,
      Finset.mem_erase,List.mem_toFinset,hnext]
    tauto
  unfold livePotential
  rw [he]
  exact Finset.sum_sdiff hsub

lemma block_weight_charge {n : ℕ} (scores : Vector ℕ n) (vertices : List (Fin n))
    (hn : vertices.Nodup) (keep : Fin n) (hk : keep∈vertices) (hsize : 2≤vertices.length)
    (hmin : ∀v∈vertices, scores[keep.val]≤scores[v.val]) :
    vertices.length+(vertices.map (fun v=>scores[v.val])).sum ≤
      2*(∑v∈vertices.toFinset.erase keep, (scores[v.val]+1)) := by
  have hc := ExtractionCharge.block_charge (fun v : Fin n=>scores[v.val]+1) vertices.toFinset keep
    (List.mem_toFinset.mpr hk) (by simpa [List.toFinset_card_of_nodup hn] using hsize)
    (by intro v hv;exact Nat.add_le_add_right (hmin v (List.mem_toFinset.mp hv)) 1)
  rw [List.sum_toFinset _ hn] at hc
  have he (vs : List (Fin n)) : (vs.map (fun v=>scores[v.val]+1)).sum =
      (vs.map (fun v=>scores[v.val])).sum+vs.length := by
    induction vs with
    | nil => simp
    | cons v vs ih => simp only [List.map_cons,List.sum_cons,List.length_cons];omega
  dsimp only at hc
  rw [he vertices] at hc
  omega

/-- Complete actual block cost telescopes against permanently removed original
rows. The additive one pays for empty/singleton branch dispatch. -/
theorem contractList_charge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) (scores : Vector ℕ n)
    (hscore : ∀v : Fin n, scores[v.val]=rows[v.val].length)
    (vertices : List (Fin n)) (hs : vertices.Nodup) (hne : vertices≠[]) (s : Working n)
    (I : ModuleExecution.Interpretation G s.store)
    (hlive : ∀v∈vertices, s.store.alive[v.val]=true)
    (hmodule : GraphModule (ModuleExecution.liveGraph G s.store)
      (ModuleExecution.liveModule s.store vertices : Set (ModuleExecution.Live s.store)))
    (hfree : P4Free ((ModuleExecution.liveGraph G s.store).induce
      (ModuleExecution.liveModule s.store vertices : Set (ModuleExecution.Live s.store)))) :
    ∃out, (contractList G rows hr hn scores vertices hs s).value=some out ∧
      Nonempty (ModuleExecution.Interpretation G out.state.store) ∧
      out.kept∈vertices ∧
      (∀v, out.state.store.alive[v.val]=true ↔
        s.store.alive[v.val]=true ∧ (v=out.kept ∨ v∉vertices)) ∧
      (contractList G rows hr hn scores vertices hs s).accesses+
        1000*livePotential scores out.state.store.alive ≤ 1000*livePotential scores s.store.alive+1 := by
  obtain ⟨out,ho,hi,hk,hmin,ha⟩ := contractList_correct G rows hr hn scores vertices hs hne s I hlive hmodule hfree
  refine ⟨out,ho,hi,hk,ha,?_⟩
  have hp := mask_potential scores s.store.alive out.state.store.alive vertices out.kept hlive ha
  have hc := contractList_accesses G rows hr hn scores vertices hs s hlive hfree
  by_cases hsz : vertices.length≤1
  · rw [if_pos hsz] at hc
    omega
  · rw [if_neg hsz] at hc
    have hw := block_weight_charge scores vertices hs out.kept hk (by omega) hmin
    have he : vertices.map (fun v=>scores[v.val])=vertices.map (fun v=>rows[v.val].length) := by
      apply List.map_congr_left
      intro v hv
      exact hscore v
    rw [he] at hw
    omega

/-- A literal pendant deletion also spends one positive vertex unit. -/
lemma absorb_charge {n : ℕ} (scores : Vector ℕ n) (s : ModuleExecution.Store n)
    (keep removed : Fin n) (hv : s.alive[removed.val]=true) :
    (ModuleExecution.absorb s keep removed).accesses+
      1000*livePotential scores (ModuleExecution.absorb s keep removed).value.alive ≤
      1000*livePotential scores s.alive := by
  let old := Finset.univ.filter (fun v : Fin n=>s.alive[v.val]=true)
  have hm : removed∈old := by simp [old,hv]
  have he : Finset.univ.filter (fun v : Fin n=>(ModuleExecution.absorb s keep removed).value.alive[v.val]=true) =
      old.erase removed := by
    ext v
    simp only [old,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase,ModuleExecution.absorb_alive]
    tauto
  have hp := Finset.sum_erase_add old (fun v : Fin n=>scores[v.val]+1) hm
  dsimp only at hp
  simp only [ModuleExecution.absorb_accesses,livePotential,he]
  change 5+1000*(∑v∈old.erase removed, (scores[v.val]+1))≤1000*(∑v∈old, (scores[v.val]+1))
  omega

lemma initial_potential {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) (scores : Vector ℕ n)
    (hscore : ∀v : Fin n, scores[v.val]=rows[v.val].length) :
    livePotential scores (ModuleExecution.initial n).alive=n+2*G.edgeFinset.card := by
  simp only [livePotential,ModuleExecution.initial,Vector.getElem_replicate,Finset.filter_true]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]
  have hs : (∑v : Fin n, scores[v.val])=Adjacency.incidenceCount rows := by
    rw [CographFrontend.incidenceCount_eq_sum]
    exact Finset.sum_congr rfl (fun v _=>hscore v)
  rw [hs,Adjacency.incidenceCount_eq_degree_sum G rows hr hn,G.sum_degrees_eq_twice_card_edges]
  omega

end HiddenCircuits.DH.BlockCollapse
