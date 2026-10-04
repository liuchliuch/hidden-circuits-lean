import HiddenCircuits.GraphReduction.CliqueOriginalColors
import HiddenCircuits.GraphReduction.WeightedExpansion

/-! Literal expansion of one weight per undirected matching edge, grouped by
actual complete-graph perfect matchings on the assigned probe-color fibers. -/
namespace HiddenCircuits.GraphReduction
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V I : Type*} [Fintype V] [Fintype I]

/-- A genuine undirected matching has one weight factor, not two, for each edge. -/
noncomputable def partnerWeight {G : SimpleGraph V} (w : V → V → ℚ) (p : PerfectPartner G) : ℚ :=
  ∏ e : PartnerEdge p, w e.val (p.val e.val)

/-- Weighted perfect matchings of the complete simple graph on the actual vertices. -/
noncomputable def weightedPerfectMatchingCount (w : V → V → ℚ) : ℚ :=
  ∑ p : PerfectPartner (⊤ : SimpleGraph V), partnerWeight w p

/-- The sum is exactly a sum over mathlib's genuine perfect matching subgraphs. -/
theorem weightedPerfectMatchingCount_graph (w : V → V → ℚ) :
    weightedPerfectMatchingCount w =
      ∑ m : PerfectMatching (⊤ : SimpleGraph V), partnerWeight w m.toPartner :=
  ((perfectPartnerEquiv (⊤ : SimpleGraph V)).sum_comp (partnerWeight w)).symm

/-- Subtraction counts each shared probe neighborhood independently, including overlaps. -/
noncomputable def cliqueProbeWeight (G : SimpleGraph V) (A : I → V → Prop) (v w : V) : ℚ :=
  (if G.Adj v w then 1 else 0) - ∑ i, if A i v ∧ A i w then 1 else 0

 theorem cliqueProbeWeight_symmetric (G : SimpleGraph V) (A : I → V → Prop) :
    ∀ v w, cliqueProbeWeight G A v w=cliqueProbeWeight G A w v := by
  intro v w
  simp only [cliqueProbeWeight,G.adj_comm,and_comm]

noncomputable instance (G : SimpleGraph V) (A : I → V → Prop) :
    Fintype (CliqueEdgeColoredMatching G A) := by
  unfold CliqueEdgeColoredMatching
  infer_instance

noncomputable def cliqueEdgeSign {G : SimpleGraph V} {A : I → V → Prop}
    (d : CliqueEdgeColoredMatching G A) : ℚ := ∏ e, colorWeight (d.2.val e)

 theorem cliqueProbeWeight_colorSum (G : SimpleGraph V) (A : I → V → Prop) (v w : V) :
    cliqueProbeWeight G A v w =
      ∑ i : Option I, if cliqueColoredEdge G A i v w then colorWeight i else 0 := by
  rw [Fintype.sum_option]
  simp only [cliqueProbeWeight,cliqueColoredEdge,colorWeight]
  rw [sub_eq_add_neg,← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> norm_num

/-- The ordinary product-of-sums expansion, with a separate color for each actual edge. -/
theorem weightedPerfectMatchingCount_expansion (G : SimpleGraph V) (A : I → V → Prop) :
    weightedPerfectMatchingCount (cliqueProbeWeight G A) =
      ∑ d : CliqueEdgeColoredMatching G A, cliqueEdgeSign d := by
  unfold weightedPerfectMatchingCount partnerWeight
  change _ = ∑ d : (Σ p : PerfectPartner (⊤ : SimpleGraph V),
    {f : PartnerEdge p → Option I // ∀ e, cliqueColoredEdge G A (f e) e.val (p.val e.val)}),
      cliqueEdgeSign d
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro p _
  simp_rw [cliqueProbeWeight_colorSum]
  rw [Fintype.prod_sum]
  have ht (f : PartnerEdge p → Option I) :
      (∏ e, if cliqueColoredEdge G A (f e) e.val (p.val e.val) then colorWeight (f e) else 0) =
      if ∀ e, cliqueColoredEdge G A (f e) e.val (p.val e.val) then
        (∏ e, colorWeight (f e)) else 0 := Fintype.prod_ite_zero
  simp_rw [ht]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) (fun (f : PartnerEdge p → Option I) => ∏ e, colorWeight (f e))

 theorem partnerColorSign_fibers {G : SimpleGraph V} (p : PerfectPartner G)
    (c : V → Option I) (hc : ∀ v, c (p.val v)=c v) :
    (∏ e : PartnerEdge p, colorWeight (c e.val)) =
      ∏ i, (-1 : ℚ) ^ (Fintype.card (CliqueFiber c (some i))/2) := by
  rw [← Fintype.prod_fiberwise' (fun e : PartnerEdge p => c e.val) colorWeight,
    Fintype.prod_option]
  simp only [colorWeight,Finset.prod_const,Finset.card_univ,one_pow,one_mul]
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  have hh : Fintype.card (CliqueFiber c (some i)) =
      2*Fintype.card {e : PartnerEdge p // c e.val=some i} := by
    convert coloredEdgeFiber_card p c hc (some i) using 1 <;> congr!
  omega

noncomputable def evenCliqueSign {A : I → V → Prop} (c : EvenCliqueColors A) : ℚ :=
  ∏ i, (-1 : ℚ)^cliqueHalf c i

 theorem cliqueEdgeSign_blocks (G : SimpleGraph V) (A : I → V → Prop)
    (d : CliqueEdgeColoredMatching G A) :
    cliqueEdgeSign d=evenCliqueSign ((cliqueEdgeBlocksEquiv G A) d).1 := by
  change _ = ∏ i, (-1 : ℚ) ^ (Fintype.card (CliqueFiber d.vertexColor (some i))/2)
  rw [← partnerColorSign_fibers d.1 d.vertexColor d.vertexColor_partner]
  unfold cliqueEdgeSign
  apply Finset.prod_congr rfl
  intro e _
  congr 1
  exact (congrArg d.2.val (edgeRep_of_edge d.1 e)).symm

 theorem cliqueOriginalBlocks_card (G : SimpleGraph V) (A : I → V → Prop)
    (c : EvenCliqueColors A) :
    Fintype.card (CliqueOriginalBlocks G A c.val) =
      perfectMatchingCount (G.induce {v | c.val.val v=none}) *
        ∏ i, oddFactorial (cliqueHalf c i) := by
  unfold CliqueOriginalBlocks
  rw [Fintype.card_prod,Fintype.card_pi,perfectMatchingCount_eq_partners]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact completePartner_card_even _ (cliqueHalf_spec c i)

/-- The undirected color expansion needed for the formal negative clique-probe sample. -/
theorem weightedPerfectMatchingCount_clique_blocks (G : SimpleGraph V) (A : I → V → Prop) :
    weightedPerfectMatchingCount (cliqueProbeWeight G A) =
      ∑ c : EvenCliqueColors A,
        (perfectMatchingCount (G.induce {v | c.val.val v=none}) : ℚ) *
          ∏ i, (-1 : ℚ)^cliqueHalf c i * (oddFactorial (cliqueHalf c i) : ℚ) := by
  rw [weightedPerfectMatchingCount_expansion]
  have h := (cliqueEdgeBlocksEquiv G A).sum_comp (fun d => evenCliqueSign d.1)
  simp only [← cliqueEdgeSign_blocks] at h
  rw [h,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c _
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,cliqueOriginalBlocks_card,
    Nat.cast_mul,Nat.cast_prod,evenCliqueSign]
  rw [Finset.prod_mul_distrib]
  ring

end HiddenCircuits.GraphReduction
