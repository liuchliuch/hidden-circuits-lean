import HiddenCircuits.DH.ModuleMerge
import HiddenCircuits.DH.ExtractionCharge

/-! Static BFS-layer scheduling invariants for ordinary-input module contraction.
All set restrictions are literal vertex deletions, not supplied pruning certificates. -/
namespace HiddenCircuits.DH.LayerSchedule
open SimpleGraph
variable {V I : Type*} [DecidableEq V]

/-- A smallest original member of a laminar family remains minimal after arbitrary
common vertex deletions, provided the surviving family members are nonempty. -/
theorem restricted_minimal (P : I → Finset V) (alive : Finset V) (indices : Set I) (u : I)
    (hu : u∈indices)
    (hlam : ∀ i ∈ indices, ∀ j ∈ indices,
      Disjoint (P i) (P j) ∨ P i ⊆ P j ∨ P j ⊆ P i)
    (hsize : ∀ i ∈ indices, (P u).card ≤ (P i).card)
    (hne : ∀ i ∈ indices, (P i ∩ alive).Nonempty) :
    ∀ i ∈ indices, P i ∩ alive ⊆ P u ∩ alive → P u ∩ alive ⊆ P i ∩ alive := by
  intro i hi hsub
  rcases hlam u hu i hi with hd | hs | hs
  · obtain ⟨v,hv⟩ := hne i hi
    exact False.elim (Finset.disjoint_left.mp hd (Finset.mem_inter.mp (hsub hv)).1
      (Finset.mem_inter.mp hv).1)
  · exact Finset.inter_subset_inter hs Finset.Subset.rfl
  · have he : P i=P u := Finset.eq_of_subset_of_card_le hs (hsize i hi)
    rw [he]

/-- The same static size ordering gives a stronger pairwise inclusion-or-disjointness rule. -/
theorem restricted_order (P Q alive : Finset V)
    (hlam : Disjoint P Q ∨ P ⊆ Q ∨ Q ⊆ P) (hcard : P.card ≤ Q.card) :
    Disjoint (P ∩ alive) (Q ∩ alive) ∨ P ∩ alive ⊆ Q ∩ alive := by
  rcases hlam with hd | hs | hs
  · exact Or.inl (hd.mono Finset.inter_subset_left Finset.inter_subset_left)
  · exact Or.inr (Finset.inter_subset_inter hs Finset.Subset.rfl)
  · have he : Q=P := Finset.eq_of_subset_of_card_le hs hcard
    exact Or.inr (by rw [he])

/-- Once at most one vertex remains in each original same-layer component, there
are no same-layer edges, regardless of how the components were enumerated. -/
theorem layer_independent_of_component_unique (G : SimpleGraph V) (layer alive : Set V)
    (hunique : ∀ a b : layer, a.val∈alive → b.val∈alive →
      (G.induce layer).Reachable a b → a.val=b.val) :
    ∀ a ∈ layer, a∈alive → ∀ b ∈ layer, b∈alive → ¬G.Adj a b := by
  intro a ha hla b hb hlb hab
  exact hab.ne (hunique ⟨a,ha⟩ ⟨b,hb⟩ hla hlb ((show (G.induce layer).Adj ⟨a,ha⟩ ⟨b,hb⟩ from hab).reachable))

/-- At a farthest independent positive layer, a unique predecessor is the vertex's
unique graph neighbor; the next operation is a literal pendant merge. -/
theorem pendant_of_unique_predecessor (G : SimpleGraph V) (r u keep : V) (k : ℕ)
    (hlevel : G.dist r u=k) (hmax : ∀ v, G.dist r v ≤ k)
    (hind : ∀ v, G.dist r v=k → ¬G.Adj u v)
    (hp : predecessors G r u = {keep}) : PendantPair G keep u := by
  have hkeep : keep∈predecessors G r u := by rw [hp]; exact Set.mem_singleton _
  refine ⟨hkeep.1.symm,?_⟩
  intro v huv
  have hpred : v∈predecessors G r u := by
    refine ⟨huv.symm,?_⟩
    have hd := huv.diff_dist_adj (u := r)
    have hm := hmax v
    have hneq : G.dist r v≠k := fun he => hind v he huv
    omega
  simpa only [hp,Set.mem_singleton_iff] using hpred

end HiddenCircuits.DH.LayerSchedule
