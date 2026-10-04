import HiddenCircuits.GraphReduction.ColoredPerfectPartner

/-! One representative of each actual undirected matching edge. The finite rank is
used only to orient an edge for its single factor in a product. -/
namespace HiddenCircuits.GraphReduction
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable def partnerRank (v : V) : Fin (Fintype.card V) := Fintype.equivFin V v
 theorem partnerRank_injective : Function.Injective (partnerRank (V:=V)) :=
  (Fintype.equivFin V).injective

def PartnerEdge (p : PerfectPartner G) := {v : V // partnerRank v < partnerRank (p.val v)}
noncomputable instance (p : PerfectPartner G) : Fintype (PartnerEdge p) := by
  classical
  unfold PartnerEdge
  infer_instance

 theorem partner_ne (p : PerfectPartner G) (v : V) : p.val v ≠ v :=
  fun h => G.irrefl (h ▸ p.property.2 v)

noncomputable def edgeRep (p : PerfectPartner G) (v : V) : PartnerEdge p := by
  classical
  exact if h : partnerRank v < partnerRank (p.val v) then ⟨v,h⟩ else
    ⟨p.val v, by
      rw [p.property.1 v]
      have hn : partnerRank (p.val v) ≠ partnerRank v :=
        fun he => partner_ne p v (partnerRank_injective he)
      exact lt_of_le_of_ne (le_of_not_gt h) hn⟩

 theorem edgeRep_of_edge (p : PerfectPartner G) (e : PartnerEdge p) : edgeRep p e.val=e := by
  classical
  unfold edgeRep
  rw [dif_pos e.property]
  rfl

 theorem edgeRep_partner (p : PerfectPartner G) (v : V) : edgeRep p (p.val v)=edgeRep p v := by
  classical
  apply Subtype.ext
  unfold edgeRep
  by_cases h : partnerRank v < partnerRank (p.val v)
  · have hn : ¬partnerRank (p.val v) < partnerRank (p.val (p.val v)) := by
      rw [p.property.1 v]
      exact not_lt_of_gt h
    simp only [dif_pos h,dif_neg hn]
    exact p.property.1 v
  · rw [dif_neg h,dif_pos (by
      rw [p.property.1 v]
      have hn : partnerRank (p.val v) ≠ partnerRank v :=
        fun he => partner_ne p v (partnerRank_injective he)
      exact lt_of_le_of_ne (le_of_not_gt h) hn)]

 theorem edgeRep_cases (p : PerfectPartner G) (v : V) :
    (edgeRep p v).val=v ∨ (edgeRep p v).val=p.val v := by
  classical
  unfold edgeRep
  split_ifs <;> simp

 theorem edgeRep_value_eq_iff (p : PerfectPartner G) (v : V) :
    (edgeRep p v).val=v ↔ partnerRank v < partnerRank (p.val v) := by
  constructor
  · intro h
    have he := (edgeRep p v).property
    rwa [h] at he
  · intro h
    exact congrArg Subtype.val (edgeRep_of_edge p ⟨v,h⟩)

/-- Every vertex is uniquely one of the two endpoints of exactly one matching edge. -/
noncomputable def partnerVertexEquiv (p : PerfectPartner G) : V ≃ PartnerEdge p × Bool where
  toFun v := (edgeRep p v, decide ((edgeRep p v).val ≠ v))
  invFun e := if e.2 then p.val e.1.val else e.1.val
  left_inv v := by
    classical
    by_cases h : (edgeRep p v).val=v
    · simp [h]
    · simp only [h,ne_eq,not_false_eq_true,decide_true,ite_true]
      obtain h'|h' := edgeRep_cases p v
      · exact (h h').elim
      · rw [h',p.property.1 v]
  right_inv e := by
    classical
    rcases e with ⟨e,b⟩
    cases b
    · simp [edgeRep_of_edge]
    · simp [edgeRep_partner,edgeRep_of_edge,Ne.symm (partner_ne p e.val)]

 theorem edgeRep_color {I : Type*} (p : PerfectPartner G) (c : V → I)
    (hc : ∀ v, c (p.val v)=c v) (v : V) : c (edgeRep p v).val=c v := by
  obtain h|h := edgeRep_cases p v
  · rw [h]
  · rw [h,hc]

/-- Independent edge colors are equivalent to vertex colors constant on actual partners. -/
noncomputable def edgeColorEquiv (p : PerfectPartner G) (I : Type*) :
    (PartnerEdge p → I) ≃ {c : V → I // ∀ v, c (p.val v)=c v} where
  toFun f := ⟨fun v => f (edgeRep p v),fun v => congrArg f (edgeRep_partner p v)⟩
  invFun c e := c.val e.val
  left_inv f := by funext e; exact congrArg f (edgeRep_of_edge p e)
  right_inv c := by
    apply Subtype.ext
    funext v
    exact edgeRep_color p c.val c.property v

noncomputable def coloredEdgeFiberEquiv {I : Type*} (p : PerfectPartner G)
    (c : V → I) (hc : ∀ v, c (p.val v)=c v) (i : I) :
    {v // c v=i} ≃ {e : PartnerEdge p // c e.val=i} × Bool where
  toFun v := (⟨edgeRep p v.val,(edgeRep_color p c hc v.val).trans v.property⟩,
    (partnerVertexEquiv p v.val).2)
  invFun e := ⟨(partnerVertexEquiv p).symm (e.1.val,e.2),by
    change c (if e.2 then p.val e.1.val.val else e.1.val.val)=i
    cases e.2 <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · exact e.1.property
    · exact (hc _).trans e.1.property⟩
  left_inv v := by
    apply Subtype.ext
    exact (partnerVertexEquiv p).symm_apply_apply v.val
  right_inv e := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst ((partnerVertexEquiv p).apply_symm_apply (e.1.val,e.2))
    · change ((partnerVertexEquiv p) ((partnerVertexEquiv p).symm (e.1.val,e.2))).2=e.2
      exact congrArg Prod.snd ((partnerVertexEquiv p).apply_symm_apply (e.1.val,e.2))

 theorem coloredEdgeFiber_card {I : Type*} (p : PerfectPartner G)
    (c : V → I) (hc : ∀ v, c (p.val v)=c v) (i : I) :
    Fintype.card {v // c v=i} = 2*Fintype.card {e : PartnerEdge p // c e.val=i} := by
  classical
  rw [Fintype.card_congr (coloredEdgeFiberEquiv p c hc i),Fintype.card_prod,Fintype.card_bool]
  omega

end HiddenCircuits.GraphReduction
