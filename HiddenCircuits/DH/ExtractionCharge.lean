import HiddenCircuits.DH.LinearBuckets

/-! Amortizing induced-subgraph extraction over actual vertex deletions.
Choosing a minimum-original-degree survivor prevents repeated survivor scans from becoming quadratic. -/
namespace HiddenCircuits.DH.ExtractionCharge
open scoped BigOperators

structure Choice (n : ℕ) where
  vertex : Fin n
  accesses : ℕ

/-- One fixed degree-array scan chooses a survivor; no induced-subgraph recognition is hidden here. -/
def chooseFrom {n : ℕ} (scores : Vector ℕ n) (best : Fin n) : List (Fin n) → Choice n
  | [] => ⟨best,0⟩
  | v::vs =>
      let q := chooseFrom scores (if scores[v.val] < scores[best.val] then v else best) vs
      ⟨q.vertex,q.accesses+4⟩

lemma chooseFrom_accesses {n : ℕ} (scores : Vector ℕ n) (best : Fin n) (vs : List (Fin n)) :
    (chooseFrom scores best vs).accesses = 4*vs.length := by
  induction vs generalizing best with
  | nil => rfl
  | cons v vs ih => simp [chooseFrom,ih]; omega

lemma chooseFrom_spec {n : ℕ} (scores : Vector ℕ n) (best : Fin n) (vs : List (Fin n)) :
    ((chooseFrom scores best vs).vertex = best ∨ (chooseFrom scores best vs).vertex ∈ vs) ∧
      scores[(chooseFrom scores best vs).vertex.val] ≤ scores[best.val] ∧
      ∀ v ∈ vs, scores[(chooseFrom scores best vs).vertex.val] ≤ scores[v.val] := by
  induction vs generalizing best with
  | nil => exact ⟨Or.inl rfl,le_rfl,by simp⟩
  | cons v vs ih =>
    by_cases hv : scores[v.val] < scores[best.val]
    · have h := ih v
      simp only [chooseFrom,hv,↓reduceIte]
      refine ⟨?_,h.2.1.trans (Nat.le_of_lt hv),?_⟩
      · rcases h.1 with he | he
        · exact Or.inr (List.mem_cons.mpr (Or.inl he))
        · exact Or.inr (List.mem_cons_of_mem _ he)
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact h.2.1
        · exact h.2.2 u hu
    · have h := ih best
      simp only [chooseFrom,hv,↓reduceIte]
      refine ⟨?_,h.2.1,?_⟩
      · exact h.1.imp_right (List.mem_cons_of_mem _)
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact h.2.1.trans (Nat.le_of_not_gt hv)
        · exact h.2.2 u hu

/-- The original row length of the chosen survivor is paid for by any other deleted vertex. -/
theorem block_charge {V : Type*} [DecidableEq V] (weight : V → ℕ) (S : Finset V) (keep : V)
    (hk : keep ∈ S) (hsize : 2 ≤ S.card) (hmin : ∀ v ∈ S, weight keep ≤ weight v) :
    ∑ v ∈ S, weight v ≤ 2*∑ v ∈ S.erase keep, weight v := by
  have hnonempty : (S.erase keep).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hk]
    omega
  obtain ⟨v,hv⟩ := hnonempty
  have hpay : weight keep ≤ ∑ u ∈ S.erase keep, weight u :=
    (hmin v (Finset.mem_of_mem_erase hv)).trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hv)
  have hsum := Finset.sum_erase_add S weight hk
  omega

/-- Pairwise-disjoint deleted sets can spend each original vertex's row length only once. -/
lemma deleted_sum_le {V : Type*} [DecidableEq V] (weight : V → ℕ) (sets : List (Finset V))
    (original : Finset V) (hd : sets.Pairwise Disjoint) (hs : ∀ S ∈ sets, S ⊆ original) :
    (sets.map (fun S => ∑ v ∈ S, weight v)).sum ≤ ∑ v ∈ original, weight v := by
  induction sets generalizing original with
  | nil => simp
  | cons S sets ih =>
    obtain ⟨hdis,hd⟩ := List.pairwise_cons.mp hd
    have hS := hs S List.mem_cons_self
    have ht : ∀ T ∈ sets, T ⊆ original \ S := by
      intro T hT v hv
      refine Finset.mem_sdiff.mpr ⟨hs T (List.mem_cons_of_mem _ hT) hv,?_⟩
      exact fun hvS => Finset.disjoint_left.mp (hdis T hT) hvS hv
    have hrest := ih (original \ S) hd ht
    have hsum := Finset.sum_sdiff hS (f := weight)
    simp only [List.map_cons,List.sum_cons]
    omega

/-- Complete extraction-scan bound for nontrivial contraction blocks. Each block must
retain a minimum-weight member, and its other vertices must be deleted permanently. -/
theorem total_charge {V : Type*} [DecidableEq V] (weight : V → ℕ)
    (blocks : List (Finset V × V)) (original : Finset V)
    (hblocks : ∀ B ∈ blocks, B.2 ∈ B.1 ∧ 2 ≤ B.1.card ∧ ∀ v ∈ B.1, weight B.2 ≤ weight v)
    (hdeleted : (blocks.map (fun B => B.1.erase B.2)).Pairwise Disjoint)
    (hsub : ∀ B ∈ blocks, B.1.erase B.2 ⊆ original) :
    (blocks.map (fun B => ∑ v ∈ B.1, weight v)).sum ≤ 2*∑ v ∈ original, weight v := by
  have hlocal : (blocks.map (fun B => ∑ v ∈ B.1, weight v)).sum ≤
      2*(blocks.map (fun B => ∑ v ∈ B.1.erase B.2, weight v)).sum := by
    induction blocks with
    | nil => simp
    | cons B blocks ih =>
      have hB := hblocks B List.mem_cons_self
      have hb := block_charge weight B.1 B.2 hB.1 hB.2.1 hB.2.2
      have ht := ih (fun B h => hblocks B (List.mem_cons_of_mem _ h))
        (List.pairwise_cons.mp hdeleted).2 (fun B h => hsub B (List.mem_cons_of_mem _ h))
      simp only [List.map_cons,List.sum_cons]
      omega
  have hglobal := deleted_sum_le weight (blocks.map (fun B => B.1.erase B.2)) original hdeleted (by
    intro S hS
    obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hS
    exact hsub B hB)
  simp only [List.map_map,Function.comp_def] at hglobal
  omega

/-- With ordinary duplicate-free graph adjacency rows, all repeated induced-block row scans
cost at most four times the original number of edges. -/
theorem graph_total_charge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : LinearBuckets.Adjacency.Represents G rows)
    (hn : ∀ v : Fin n, (rows[v.val]).Nodup) (blocks : List (Finset (Fin n) × Fin n))
    (hblocks : ∀ B ∈ blocks, B.2 ∈ B.1 ∧ 2 ≤ B.1.card ∧
      ∀ v ∈ B.1, (rows[B.2.val]).length ≤ (rows[v.val]).length)
    (hdeleted : (blocks.map (fun B => B.1.erase B.2)).Pairwise Disjoint) :
    (blocks.map (fun B => ∑ v ∈ B.1, (rows[v.val]).length)).sum ≤ 4*G.edgeFinset.card := by
  have hc := total_charge (fun v => (rows[v.val]).length) blocks Finset.univ hblocks hdeleted
    (fun _ _ => Finset.subset_univ _)
  have hi : (∑ v : Fin n, (rows[v.val]).length) = LinearBuckets.Adjacency.incidenceCount rows := by
    simp only [LinearBuckets.Adjacency.incidenceCount,LinearBuckets.Adjacency.entriesFrom_values,
      List.length_flatMap,List.length_map]
    rw [← List.ofFn_eq_map,List.sum_ofFn]
  rw [hi,LinearBuckets.Adjacency.incidenceCount_eq_degree_sum G rows hr hn,
    G.sum_degrees_eq_twice_card_edges] at hc
  simpa only [← Nat.mul_assoc] using hc

end HiddenCircuits.DH.ExtractionCharge
