import HiddenCircuits.GraphReduction.CliqueWeightedExpansion

/-! Zero-one undirected weights give exactly the actual simple graph matching count. -/
namespace HiddenCircuits.GraphReduction
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

noncomputable def undirectedIndicator (G : SimpleGraph V) (v w : V) : ℚ :=
  if G.Adj v w then 1 else 0

 theorem partnerEdge_all_iff {H : SimpleGraph V} (G : SimpleGraph V) (p : PerfectPartner H) :
    (∀ e : PartnerEdge p, G.Adj e.val (p.val e.val)) ↔ ∀ v, G.Adj v (p.val v) := by
  constructor
  · intro h v
    have he := h (edgeRep p v)
    obtain hr|hr := edgeRep_cases p v
    · rwa [hr] at he
    · rw [hr,p.property.1 v] at he
      exact he.symm
  · exact fun h e => h e.val

 theorem partnerWeight_indicator {H : SimpleGraph V} (G : SimpleGraph V) (p : PerfectPartner H) :
    partnerWeight (undirectedIndicator G) p = if ∀ v, G.Adj v (p.val v) then 1 else 0 := by
  unfold partnerWeight undirectedIndicator
  simp only [Fintype.prod_boole,partnerEdge_all_iff]

noncomputable def allowedFullPartnerEquiv (G : SimpleGraph V) :
    {p : PerfectPartner (⊤ : SimpleGraph V) // ∀ v, G.Adj v (p.val v)} ≃ PerfectPartner G where
  toFun p := ⟨p.val.val,p.val.property.1,p.property⟩
  invFun p := ⟨⟨p.val,p.property.1,fun v => (p.property.2 v).ne⟩,p.property.2⟩
  left_inv p := rfl
  right_inv p := rfl

 theorem weightedPerfectMatchingCount_indicator (G : SimpleGraph V) :
    weightedPerfectMatchingCount (undirectedIndicator G)=(perfectMatchingCount G : ℚ) := by
  unfold weightedPerfectMatchingCount
  simp_rw [partnerWeight_indicator]
  rw [perfectMatchingCount_eq_partners,← Fintype.card_congr (allowedFullPartnerEquiv G)]
  simp [Fintype.card_subtype]

end HiddenCircuits.GraphReduction
