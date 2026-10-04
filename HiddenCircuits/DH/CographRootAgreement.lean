import HiddenCircuits.DH.CographPairedEnvelopes

/-! Both original two sweeps choose the same first vertex of every graph module. -/
namespace HiddenCircuits.DH
open SimpleGraph LexBFSModel
variable {V : Type*} {G : SimpleGraph V}

lemma pairwise_idxOf [DecidableEq V] (xs : List V) (hn : xs.Nodup) :
    xs.Pairwise (fun u v => xs.idxOf u < xs.idxOf v) := by
  rw [List.pairwise_iff_get]
  intro i j hij
  simpa only [List.get_idxOf hn] using hij

/-- The first sweep supplies only a tie order to the second one; module uniformity
and stable tie breaking nevertheless identify their recursive roots exactly. -/
theorem GraphModule.two_sweep_first_eq [DecidableRel G.Adj] {M : Set V}
    (hM : GraphModule G M) (tie : List V) (htie : tie.Nodup) (hall : ∀v, v∈tie)
    (normalPast : List (Event V)) (normalRoot : Event V) (normalAfter : List (Event V))
    (hnormal : sweep (fun a b => decide (G.Adj a b)) true tie = normalPast++normalRoot::normalAfter)
    (complementPast : List (Event V)) (complementRoot : Event V) (complementAfter : List (Event V))
    (hcomplement : sweep (fun a b => decide (G.Adj a b)) false
      ((sweep (fun a b => decide (G.Adj a b)) true tie).map Event.vertex) =
        complementPast++complementRoot::complementAfter)
    (hnM : normalRoot.vertex∈M) (hcM : complementRoot.vertex∈M)
    (hnfresh : ∀e∈normalPast, e.vertex∉M) (hcfresh : ∀e∈complementPast, e.vertex∉M) :
    complementRoot.vertex=normalRoot.vertex := by
  classical
  let order := (sweep (fun a b => decide (G.Adj a b)) true tie).map Event.vertex
  have hp := sweep_perm (fun a b => decide (G.Adj a b)) true tie
  have hn : order.Nodup := hp.nodup_iff.mpr htie
  have hcovered : ∀v, v∈order := fun v => hp.mem_iff.mpr (hall v)
  have horder : order=normalPast.map Event.vertex++normalRoot.vertex::normalAfter.map Event.vertex := by
    simp [order,hnormal]
  have hbefore : ∀v∈M, v∉normalPast.map Event.vertex := by
    intro v hv hm
    obtain ⟨e,he,hev⟩ := List.mem_map.mp hm
    exact hnfresh e he (hev ▸ hv)
  have hmin : ∀v∈M, order.idxOf normalRoot.vertex≤order.idxOf v := by
    intro v hv
    rw [horder,List.idxOf_append_of_notMem (hbefore normalRoot.vertex hnM),
      List.idxOf_append_of_notMem (hbefore v hv)]
    simp
  have hinj : Function.Injective (fun v => order.idxOf v) := by
    intro u v he
    exact (List.idxOf_inj (hcovered u)).mp he
  exact hM.sweep_first_eq false order (fun v => order.idxOf v) (pairwise_idxOf order hn)
    hinj (fun v _ => hcovered v) complementPast complementRoot complementAfter hcomplement
    hcM hcfresh hnM hmin

end HiddenCircuits.DH
