import HiddenCircuits.GraphReduction.UnitIntervalIntegerExtraction

/-! Internally derived feasible quadratic grid vectors aligned with an umbrella
order. This is the existence invariant for a bounded actual relaxation loop. -/
namespace HiddenCircuits.GraphReduction.UnitCoordinateExtraction
open UnitIntervalOrder FiniteOrderRank

lemma numerator_mono_value {V : Type*} [Fintype V] (D : ℕ) (hD : 0 < D)
    (u : V→ℕ) (v w : V) (h : u v ≤ u w) :
    NatUnitIntervalGrid.numerator D u v ≤ NatUnitIntervalGrid.numerator D u w := by
  have hq:u v/D ≤ u w/D:=Nat.div_le_div_right h
  by_cases he:u v/D=u w/D
  · have hv:=Nat.mod_add_div (u v) D
    have hw:=Nat.mod_add_div (u w) D
    rw [he] at hv
    have hr:u v%D ≤ u w%D:=by omega
    have hm:=FiniteOrderRank.mono (NatUnitIntervalGrid.remainderParts D u) hr
    unfold NatUnitIntervalGrid.numerator
    rw [he]
    omega
  · have hlt:u v/D < u w/D:=by omega
    have hrank:=FiniteOrderRank.strict (NatUnitIntervalGrid.quotient_mem D u v) hlt
    have hfrac:=NatUnitIntervalGrid.remainder_rank_lt D u v
    have hp:=NatUnitIntervalGrid.denominator_pos (V:=V)
    unfold NatUnitIntervalGrid.numerator
    nlinarith
lemma scaled_le {D a b : ℕ} (hD : 0 < D) :
    (a:ℚ)/D ≤ (b:ℚ)/D+1 ↔ a ≤ b+D := by
  have hp:(0:ℚ)<D:=by exact_mod_cast hD
  have he:(b:ℚ)/D+1=((b:ℚ)+D)/D:=by rw [add_div,div_self hp.ne']
  rw [he,div_le_div_iff_of_pos_right hp]
  exact_mod_cast Iff.rfl

theorem ordered_grid_witness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : Umbrella G) :
    ∃x : Fin n→ℕ, Monotone x ∧
      (∀i,x i+max 1 n < 2*n*max 1 n) ∧
      ∀i j,G.Adj i j ↔ i≠j ∧ x i ≤ x j+max 1 n ∧ x j ≤ x i+max 1 n := by
  let u:=Dyadic.numerators n G
  let D:ℕ:=2^n
  let r:=buildModel n G hG
  have hD:0<D:=by dsimp [D];positivity
  have hDq:(0:ℚ)<D:=by exact_mod_cast hD
  have hu:∀i,(u i:ℚ)/D=r.left i:=fun i=>Dyadic.numerators_refine n G hG i
  have hum:Monotone u:=by
    intro i j hij
    have h:=r.increasing.monotone hij
    rw [←hu i,←hu j] at h
    exact_mod_cast (div_le_div_iff_of_pos_right hDq).mp h
  refine ⟨NatUnitIntervalGrid.numerator D u,?_,?_,?_⟩
  · intro i j hij;exact numerator_mono_value D hD u i j (hum hij)
  · intro i;simpa [NatUnitIntervalGrid.denominator] using NatUnitIntervalGrid.endpoint_bound D u i
  · intro i j
    have hr:=r.representation.adjacency i j
    rw [UnitInterval.icc_overlap (by change r.left i ≤ r.left i+1;linarith)
      (by change r.left j ≤ r.left j+1;linarith)] at hr
    change G.Adj i j ↔ i≠j ∧ r.left i ≤ r.left j+1 ∧ r.left j ≤ r.left i+1 at hr
    rw [←hu i,←hu j,scaled_le hD,scaled_le hD] at hr
    have h₁:=NatUnitIntervalGrid.comparison D hD u i j
    have h₂:=NatUnitIntervalGrid.comparison D hD u j i
    simp only [NatUnitIntervalGrid.denominator,Fintype.card_fin] at h₁ h₂
    rw [h₁,h₂]
    exact hr

theorem permuted_grid_witness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (e : Fin n≃Fin n) (hG : Umbrella (G.comap e)) :
    ∃x : Fin n→ℕ, Monotone (x∘e) ∧
      (∀i,x i+max 1 n < 2*n*max 1 n) ∧
      ∀i j,G.Adj i j ↔ i≠j ∧ x i ≤ x j+max 1 n ∧ x j ≤ x i+max 1 n := by
  obtain ⟨u,hum,hb,ha⟩:=ordered_grid_witness (G.comap e) hG
  refine ⟨u∘e.symm,?_,?_,?_⟩
  · simpa only [Function.comp_assoc,Equiv.symm_comp_self,Function.comp_id] using hum
  · intro i;exact hb (e.symm i)
  · intro i j
    simpa only [SimpleGraph.comap_adj,Equiv.apply_symm_apply,ne_eq,e.symm.injective.eq_iff,Function.comp_def]
      using ha (e.symm i) (e.symm j)
end HiddenCircuits.GraphReduction.UnitCoordinateExtraction
