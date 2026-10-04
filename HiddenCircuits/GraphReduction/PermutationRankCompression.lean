import HiddenCircuits.GraphReduction.MonotoneQueryRepresentation

/-! Compress finite endpoint orders to their actual integer ranks, without changing crossings. -/
namespace HiddenCircuits.GraphReduction
variable {V : Type*} [Fintype V]

noncomputable def rankByOrder (f : V ↪ ℕ) (v : V) : Fin (Fintype.card V) :=
  (sortByRank f f.injective).symm v

 theorem rankByOrder_lt_iff (f : V ↪ ℕ) (v w : V) :
    (rankByOrder f v).val < (rankByOrder f w).val ↔ f v<f w := by
  have hm := sortByRank_strictMono f f.injective
  have hh := hm.lt_iff_lt (a:=rankByOrder f v) (b:=rankByOrder f w)
  simpa only [rankByOrder,Equiv.apply_symm_apply,Fin.lt_def] using hh.symm

/-- Sorting ranks are exactly finite counts of preceding endpoints. -/
theorem rankByOrder_eq_count (f : V ↪ ℕ) (v : V) :
    (rankByOrder f v).val=endpointCount f (f v) := by
  let e := sortByRank f f.injective
  have hm := sortByRank_strictMono f f.injective
  rw [← endpointCount_comp e f (f v),endpointCount_card]
  have hc : (Finset.univ.filter (fun i => f (e i)<f v)) =
      (Finset.univ.filter (fun i : Fin (Fintype.card V) => i.val<(e.symm v).val)) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    have hh := hm.lt_iff_lt (a:=i) (b:=e.symm v)
    simpa only [e,Equiv.apply_symm_apply,Fin.lt_def] using hh
  rw [hc,Fin.card_filter_val_lt,Nat.min_eq_right (Nat.le_of_lt (e.symm v).isLt)]
  rfl

/-- Finite comparison counts produce the literal endpoint ranks. -/
def PermutationDiagram.compress (D : PermutationDiagram V) : PermutationDiagram V where
  upper := ⟨fun v => endpointCount D.upper (D.upper v),by
    intro v w h
    dsimp only at h
    rw [← rankByOrder_eq_count,← rankByOrder_eq_count] at h
    exact (sortByRank D.upper D.upper.injective).symm.injective (Fin.ext h)⟩
  lower := ⟨fun v => endpointCount D.lower (D.lower v),by
    intro v w h
    dsimp only at h
    rw [← rankByOrder_eq_count,← rankByOrder_eq_count] at h
    exact (sortByRank D.lower D.lower.injective).symm.injective (Fin.ext h)⟩

@[simp] theorem PermutationDiagram.compress_graph (D : PermutationDiagram V) : D.compress.graph=D.graph := by
  ext v w
  change ((_ < _ ∧ _ < _) ∨ (_ < _ ∧ _ < _)) ↔ ((_ < _ ∧ _ < _) ∨ (_ < _ ∧ _ < _))
  simp only [compress,Function.Embedding.coeFn_mk,← rankByOrder_eq_count,rankByOrder_lt_iff]

 theorem PermutationDiagram.compress_upper_lt (D : PermutationDiagram V) (v : V) :
    D.compress.upper v < Fintype.card V := by
  change endpointCount D.upper (D.upper v)<_
  rw [← rankByOrder_eq_count]
  exact (rankByOrder D.upper v).isLt
 theorem PermutationDiagram.compress_lower_lt (D : PermutationDiagram V) (v : V) :
    D.compress.lower v < Fintype.card V := by
  change endpointCount D.lower (D.lower v)<_
  rw [← rankByOrder_eq_count]
  exact (rankByOrder D.lower v).isLt

end HiddenCircuits.GraphReduction
