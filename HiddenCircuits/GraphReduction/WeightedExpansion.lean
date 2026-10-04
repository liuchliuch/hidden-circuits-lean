import HiddenCircuits.GraphReduction.ColoredOriginal

/-! Literal expansion of the weighted complete bipartite perfect-matching sum. -/
namespace HiddenCircuits.GraphReduction
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]

noncomputable instance edgeColoredMatchingFintype (R : X → Y → Prop)
    (A : I → X → Prop) (B : I → Y → Prop) : Fintype (EdgeColoredMatching R A B) := by
  classical
  unfold EdgeColoredMatching
  infer_instance

def colorWeight : Option I → ℚ
  | none => 1
  | some _ => -1

noncomputable def assignmentSign (c : X → Option I) : ℚ := ∏ x, colorWeight (c x)

 theorem assignmentSign_fibers (c : X → Option I) :
    assignmentSign c = ∏ i, (-1 : ℚ) ^ Fintype.card (OriginalFiber c (some i)) := by
  classical
  rw [assignmentSign,← Fintype.prod_fiberwise' c colorWeight,Fintype.prod_option]
  simp [colorWeight,OriginalFiber]

/-- Original graph weight minus one for every attached probe color, counting overlaps. -/
noncomputable def probeWeight (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop)
    (x : X) (y : Y) : ℚ := by
  classical
  exact (if R x y then 1 else 0) - ∑ i, if A i x ∧ B i y then 1 else 0

/-- Weighted perfect matchings of the complete bipartite graph, encoded by their bijections. -/
noncomputable def weightedBipartiteCount (w : X → Y → ℚ) : ℚ := by
  classical
  exact ∑ e : X ≃ Y, ∏ x, w x (e x)

/-- Its summation indices are in bijection with actual perfect matching subgraphs. -/
theorem weightedBipartiteCount_graph (w : X → Y → ℚ) :
    weightedBipartiteCount w =
      ∑ m : PerfectMatching (cutGraph (fun (_ : X) (_ : Y) => True)),
        ∏ x, w x ((cutPerfectMatchingEquiv _ m).val x) := by
  classical
  let e := (cutPerfectMatchingEquiv (fun (_ : X) (_ : Y) => True)).trans (trueCutBijectionEquiv X Y)
  exact (e.sum_comp (fun f : X ≃ Y => ∏ x, w x (f x))).symm

 theorem probeWeight_colorSum (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop)
    (x : X) (y : Y) :
    probeWeight R A B x y =
      ∑ i : Option I, if coloredEdge R A B (fun _ => i) x y then colorWeight i else 0 := by
  classical
  rw [Fintype.sum_option]
  simp only [probeWeight,coloredEdge,colorWeight]
  rw [sub_eq_add_neg,← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> norm_num

 theorem weightedBipartiteCount_expansion (R : X → Y → Prop)
    (A : I → X → Prop) (B : I → Y → Prop) :
    weightedBipartiteCount (probeWeight R A B) =
      ∑ d : EdgeColoredMatching R A B, assignmentSign d.2.val := by
  classical
  unfold weightedBipartiteCount
  change _ = ∑ d : (Σ e : X ≃ Y, {c : X → Option I // ∀ x, coloredEdge R A B c x (e x)}), assignmentSign d.2.val
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro e _
  simp_rw [probeWeight_colorSum]
  rw [Fintype.prod_sum]
  have ht (c : X → Option I) :
      (∏ x, if coloredEdge R A B (fun _ => c x) x (e x) then colorWeight (c x) else 0) =
      if ∀ x, coloredEdge R A B c x (e x) then assignmentSign c else 0 := by
    change (∏ x, if coloredEdge R A B c x (e x) then colorWeight (c x) else 0) = _
    exact Fintype.prod_ite_zero
  simp_rw [ht]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) assignmentSign

 theorem originalColorBlocks_card (R : X → Y → Prop) (A : I → X → Prop)
    (B : I → Y → Prop) (cd : BalancedColors A B) :
    Fintype.card (OriginalColorBlocks R A B cd.val) =
      Fintype.card (OriginalResidual R cd.val.val) *
        ∏ i, (Fintype.card (OriginalFiber cd.val.val.1 (some i))).factorial := by
  classical
  unfold OriginalColorBlocks
  rw [Fintype.card_prod,Fintype.card_pi]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact Fintype.card_equiv (Fintype.equivOfCardEq (cd.property i))

/-- Grouping the edge expansion by disjoint vertex colors yields exactly the factorial block sum. -/
theorem weightedBipartiteCount_blocks (R : X → Y → Prop)
    (A : I → X → Prop) (B : I → Y → Prop) :
    weightedBipartiteCount (probeWeight R A B) =
      ∑ cd : BalancedColors A B, (Fintype.card (OriginalResidual R cd.val.val) : ℚ) *
        ∏ i, (-1 : ℚ) ^ Fintype.card (OriginalFiber cd.val.val.1 (some i)) *
          ((Fintype.card (OriginalFiber cd.val.val.1 (some i))).factorial : ℚ) := by
  classical
  rw [weightedBipartiteCount_expansion]
  have h := (edgeColoredBlocksEquiv R A B).sum_comp
    (fun d => assignmentSign d.1.val.val.1)
  change (∑ d : EdgeColoredMatching R A B, assignmentSign d.2.val) = _ at h
  rw [h,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro cd _
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,originalColorBlocks_card,
    Nat.cast_mul,Nat.cast_prod,assignmentSign_fibers]
  rw [Finset.prod_mul_distrib]
  ring

end HiddenCircuits.GraphReduction
