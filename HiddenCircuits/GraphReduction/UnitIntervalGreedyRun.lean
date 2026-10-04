import HiddenCircuits.GraphReduction.UnitIntervalGreedyPick

/-! The bounded ordinary-graph greedy component scan. Every iteration appends
one actual vertex; an empty frontier terminates the component. -/
namespace HiddenCircuits.GraphReduction.UnitIntervalGreedy
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]

def run : ℕ → List V → Finset V → List V × Finset V
  | 0,ls,R => (ls,R)
  | fuel+1,ls,R =>
    match choose G ls.toFinset R with
    | none => (ls,R)
    | some y => if score G ls.toFinset y = 0 then (ls,R)
      else run fuel (ls++[y]) (R.erase y)

/-- A concrete scan forced to begin at the specified vertex. -/
def component (root : V) : List V :=
  (run G (Fintype.card V) [root] (Finset.univ.erase root)).1

lemma run_subset (fuel : ℕ) (ls : List V) (R : Finset V) : (run G fuel ls R).2 ⊆ R := by
  induction fuel generalizing ls R with
  | zero => exact Finset.Subset.refl _
  | succ fuel ih =>
    simp only [run]
    split
    · exact Finset.Subset.refl _
    · split
      · exact Finset.Subset.refl _
      · exact (ih _ _).trans (Finset.erase_subset _ _)

lemma run_prefix (fuel : ℕ) (ls : List V) (R : Finset V) : ls.IsPrefix (run G fuel ls R).1 := by
  induction fuel generalizing ls R with
  | zero => exact List.prefix_refl _
  | succ fuel ih =>
    simp only [run]
    split
    · exact List.prefix_refl _
    · split
      · exact List.prefix_refl _
      · exact (List.prefix_append _ _).trans (ih _ _)

lemma run_partition (fuel : ℕ) (ls : List V) (R : Finset V)
    (hdis : ∀ v ∈ ls, v ∉ R) (hnode : ls.Nodup) :
    (run G fuel ls R).1.Nodup ∧
      (∀ v ∈ (run G fuel ls R).1, v ∉ (run G fuel ls R).2) ∧
      (run G fuel ls R).1.toFinset ∪ (run G fuel ls R).2 = ls.toFinset ∪ R := by
  induction fuel generalizing ls R with
  | zero => exact ⟨hnode,hdis,rfl⟩
  | succ fuel ih =>
    simp only [run]
    split
    · exact ⟨hnode,hdis,rfl⟩
    · rename_i y hy
      split
      · exact ⟨hnode,hdis,rfl⟩
      · have hyr := (choose_spec G ls.toFinset R hy).1
        have hyout : y ∉ ls := fun h => hdis y h hyr
        have hd : ∀ v ∈ ls++[y], v ∉ R.erase y := by
          intro v hv hvR
          rcases List.mem_append.mp hv with hv|hv
          · exact hdis v hv (Finset.mem_of_mem_erase hvR)
          · have hvy : v=y := by simpa using hv
            subst v; exact (Finset.mem_erase.mp hvR).1 rfl
        have hn : (ls++[y]).Nodup := by
          simp only [List.nodup_append,hnode,List.nodup_singleton,true_and,List.mem_singleton,forall_eq]
          intro a ha he
          exact hyout (he ▸ ha)
        obtain ⟨hn,hd,hu⟩ := ih (ls++[y]) (R.erase y) hd hn
        refine ⟨hn,hd,hu.trans ?_⟩
        ext v
        simp only [List.toFinset_append,List.toFinset_cons,List.toFinset_nil,Finset.union_empty,
          Finset.mem_union,Finset.mem_insert,Finset.notMem_empty,or_false,Finset.mem_erase]
        by_cases hvy : v=y
        · subst v; simp [hyr]
        · simp [hvy]

lemma run_frontier (fuel : ℕ) (ls : List V) (R : Finset V) (hf : R.card ≤ fuel) :
    ∀ v ∈ (run G fuel ls R).2, score G (run G fuel ls R).1.toFinset v = 0 := by
  induction fuel generalizing ls R with
  | zero =>
    have hr : R = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hf)
    simp [run,hr]
  | succ fuel ih =>
    simp only [run]
    split
    · rename_i he
      have hr : R = ∅ := (choose_none G ls.toFinset R).mp he
      simp [hr]
    · rename_i y hy
      have hyr := (choose_spec G ls.toFinset R hy).1
      split
      · rename_i hscore
        intro v hv
        have hh := ((choose_spec G ls.toFinset R hy).2 v hv).1
        change score G ls.toFinset v = 0
        omega
      · apply ih
        rw [Finset.card_erase_of_mem hyr]
        omega

end HiddenCircuits.GraphReduction.UnitIntervalGreedy

namespace HiddenCircuits.GraphReduction.UnitIntervalGreedy
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma component_root_mem (root : V) : root ∈ component G root :=
  (run_prefix G (Fintype.card V) [root] (Finset.univ.erase root)).subset (by simp)

lemma component_nodup (root : V) : (component G root).Nodup :=
  (run_partition G (Fintype.card V) [root] (Finset.univ.erase root) (by simp) (by simp)).1

/-- A terminated component scan has no edge to a vertex it did not emit. -/
lemma component_closed (root : V) {v w : V} (hv : v ∈ component G root)
    (hw : w ∉ component G root) : ¬G.Adj v w := by
  let result := run G (Fintype.card V) [root] (Finset.univ.erase root)
  have hp := run_partition G (Fintype.card V) [root] (Finset.univ.erase root) (by simp) (by simp)
  have hcover : result.1.toFinset ∪ result.2 = Finset.univ := by
    simpa [result] using hp.2.2
  have hwR : w ∈ result.2 := by
    have hwm : w ∈ result.1.toFinset ∪ result.2 := by rw [hcover]; exact Finset.mem_univ _
    exact (Finset.mem_union.mp hwm).resolve_left (by simpa [result,component] using hw)
  have hf := run_frontier G (Fintype.card V) [root] (Finset.univ.erase root)
    (Finset.card_le_univ _) w hwR
  intro he
  have hm : v ∈ neighbors G result.1.toFinset w := by
    apply Finset.mem_filter.mpr
    exact ⟨by simpa [result,component] using hv,Or.inr he.symm⟩
  have hc : 0 < score G result.1.toFinset w := Finset.card_pos.mpr ⟨v,hm⟩
  change score G result.1.toFinset w = 0 at hf
  omega

end HiddenCircuits.GraphReduction.UnitIntervalGreedy
