import HiddenCircuits.GraphReduction.PartnerEdges
import HiddenCircuits.GraphReduction.CliqueProbeColors

/-! Independent colors on undirected edges restrict and glue as actual original
perfect matchings and actual complete-graph perfect matchings on the color fibers. -/
namespace HiddenCircuits.GraphReduction
attribute [local instance] Classical.propDecidable
variable {V I : Type*} [Fintype V] [Fintype I]

def cliqueColoredEdge (G : SimpleGraph V) (A : I → V → Prop) (i : Option I) (v w : V) : Prop :=
  match i with
  | none => G.Adj v w
  | some j => A j v ∧ A j w

 theorem cliqueColoredEdge_symm (G : SimpleGraph V) (A : I → V → Prop) (i : Option I) (v w : V) :
    cliqueColoredEdge G A i v w ↔ cliqueColoredEdge G A i w v := by
  cases i
  · exact G.adj_comm v w
  · exact and_comm

/-- The genuine graph allowed by a prescribed vertex color. -/
def cliqueColorGraph (G : SimpleGraph V) (A : I → V → Prop) (c : V → Option I) : SimpleGraph V where
  Adj v w := v≠w ∧ c v=c w ∧ cliqueColoredEdge G A (c v) v w
  symm := by
    intro v w h
    refine ⟨h.1.symm,h.2.1.symm,?_⟩
    rw [← h.2.1]
    exact (cliqueColoredEdge_symm G A _ _ _).mp h.2.2
  loopless := ⟨fun v h => h.1 rfl⟩

def CliqueEdgeColoredMatching (G : SimpleGraph V) (A : I → V → Prop) :=
  Σ p : PerfectPartner (⊤ : SimpleGraph V),
    {f : PartnerEdge p → Option I // ∀ e, cliqueColoredEdge G A (f e) e.val (p.val e.val)}

def CliqueOriginalColorData (G : SimpleGraph V) (A : I → V → Prop) :=
  Σ c : CliqueAssignments A, ColoredPerfectPartner (cliqueColorGraph G A c.val) c.val

namespace CliqueEdgeColoredMatching
variable {G : SimpleGraph V} {A : I → V → Prop}
noncomputable def vertexColor (d : CliqueEdgeColoredMatching G A) (v : V) : Option I :=
  d.2.val (edgeRep d.1 v)
 theorem vertexColor_partner (d : CliqueEdgeColoredMatching G A) (v : V) :
    d.vertexColor (d.1.val v)=d.vertexColor v :=
  congrArg d.2.val (edgeRep_partner d.1 v)
 theorem vertexColor_allowed (d : CliqueEdgeColoredMatching G A) (v : V) :
    cliqueColoredEdge G A (d.vertexColor v) v (d.1.val v) := by
  have h := d.2.property (edgeRep d.1 v)
  change cliqueColoredEdge G A (d.vertexColor v) (edgeRep d.1 v).val
    (d.1.val (edgeRep d.1 v).val) at h
  obtain he|he := edgeRep_cases d.1 v
  · rwa [he] at h
  · rw [he,d.1.property.1 v] at h
    exact (cliqueColoredEdge_symm G A _ _ _).mp h

noncomputable def toData (d : CliqueEdgeColoredMatching G A) : CliqueOriginalColorData G A := by
  refine ⟨⟨d.vertexColor,?_⟩,⟨⟨d.1.val,d.1.property.1,?_⟩,d.vertexColor_partner⟩⟩
  · intro v i h
    have hv := d.vertexColor_allowed v
    rw [h] at hv
    exact hv.1
  · intro v
    exact ⟨Ne.symm (partner_ne d.1 v),(d.vertexColor_partner v).symm,d.vertexColor_allowed v⟩
end CliqueEdgeColoredMatching

namespace CliqueOriginalColorData
variable {G : SimpleGraph V} {A : I → V → Prop}
def fullPartner (d : CliqueOriginalColorData G A) : PerfectPartner (⊤ : SimpleGraph V) :=
  ⟨d.2.val.val,d.2.val.property.1,fun v => (d.2.val.property.2 v).1⟩
noncomputable def toEdges (d : CliqueOriginalColorData G A) : CliqueEdgeColoredMatching G A :=
  ⟨d.fullPartner,⟨fun e => d.1.val e.val,fun e => (d.2.val.property.2 e.val).2.2⟩⟩
 theorem color_toEdges (d : CliqueOriginalColorData G A) : d.toEdges.vertexColor=d.1.val := by
  funext v
  exact edgeRep_color d.fullPartner d.1.val d.2.property v
end CliqueOriginalColorData

 theorem cliqueOriginalData_ext {G : SimpleGraph V} {A : I → V → Prop}
    (d e : CliqueOriginalColorData G A) (hc : d.1.val=e.1.val)
    (hp : d.2.val.val=e.2.val.val) : d=e := by
  rcases d with ⟨⟨c,hc'⟩,⟨⟨p,hp'⟩,hpc⟩⟩
  rcases e with ⟨⟨c',hc''⟩,⟨⟨p',hp''⟩,hpc'⟩⟩
  dsimp only at hc hp
  subst c'
  subst p'
  rfl

/-- Expanding one color per actual undirected edge is bijective with the vertex-fiber data. -/
noncomputable def cliqueEdgeDataEquiv (G : SimpleGraph V) (A : I → V → Prop) :
    CliqueEdgeColoredMatching G A ≃ CliqueOriginalColorData G A where
  toFun := CliqueEdgeColoredMatching.toData
  invFun := CliqueOriginalColorData.toEdges
  left_inv d := by
    rcases d with ⟨⟨p,hp⟩,⟨f,hf⟩⟩
    refine Sigma.ext (show _ = (⟨p,hp⟩ : PerfectPartner (⊤ : SimpleGraph V)) from rfl) ?_
    apply heq_of_eq
    apply Subtype.ext
    funext e
    exact congrArg f (edgeRep_of_edge ⟨p,hp⟩ e)
  right_inv d := cliqueOriginalData_ext _ _ d.color_toEdges rfl

/-- None fibers retain precisely the original graph. -/
def cliqueOriginalNoneEquiv (G : SimpleGraph V) (A : I → V → Prop) (c : CliqueAssignments A) :
    PerfectPartner ((cliqueColorGraph G A c.val).induce {v | c.val v=none}) ≃
      PerfectPartner (G.induce {v | c.val v=none}) :=
  perfectPartnerCongr _ _ (Equiv.refl _) (by
    intro v w
    change (v.val≠w.val ∧ c.val v.val=c.val w.val ∧ cliqueColoredEdge G A (c.val v.val) v.val w.val) ↔
      G.Adj v.val w.val
    have hv : c.val v.val=none := v.property
    have hw : c.val w.val=none := w.property
    simp only [hv,hw,cliqueColoredEdge,true_and]
    exact ⟨And.right,fun h => ⟨h.ne,h⟩⟩)

/-- A nonempty probe color allows all undirected pairs in its assigned original fiber. -/
def cliqueOriginalSomeEquiv (G : SimpleGraph V) (A : I → V → Prop)
    (c : CliqueAssignments A) (i : I) :
    PerfectPartner ((cliqueColorGraph G A c.val).induce {v | c.val v=some i}) ≃
      PerfectPartner (⊤ : SimpleGraph (CliqueFiber c.val (some i))) :=
  perfectPartnerCongr _ _ (Equiv.refl _) (by
    intro v w
    change (v.val≠w.val ∧ c.val v.val=c.val w.val ∧ cliqueColoredEdge G A (c.val v.val) v.val w.val) ↔ v≠w
    have hv : c.val v.val=some i := v.property
    have hw : c.val w.val=some i := w.property
    simp only [hv,hw,cliqueColoredEdge,true_and,
      c.property v.val i v.property,c.property w.val i w.property,and_true]
    exact Subtype.coe_ne_coe)

def CliqueOriginalBlocks (G : SimpleGraph V) (A : I → V → Prop) (c : CliqueAssignments A) :=
  PerfectPartner (G.induce {v | c.val v=none}) ×
    ∀ i, PerfectPartner (⊤ : SimpleGraph (CliqueFiber c.val (some i)))
noncomputable instance (G : SimpleGraph V) (A : I → V → Prop) (c : CliqueAssignments A) :
    Fintype (CliqueOriginalBlocks G A c) := by
  unfold CliqueOriginalBlocks
  infer_instance

noncomputable def cliqueOriginalBlocksEquiv (G : SimpleGraph V) (A : I → V → Prop)
    (c : CliqueAssignments A) :
    ColoredPerfectPartner (cliqueColorGraph G A c.val) c.val ≃ CliqueOriginalBlocks G A c :=
  (coloredPerfectPartnerEquiv _ _).trans (Equiv.piOptionEquivProd.trans
    (Equiv.prodCongr (cliqueOriginalNoneEquiv G A c)
      (Equiv.piCongrRight (cliqueOriginalSomeEquiv G A c))))

 theorem cliqueOriginalBlocks_even {G : SimpleGraph V} {A : I → V → Prop}
    {c : CliqueAssignments A} (b : CliqueOriginalBlocks G A c) :
    ∀ i, Even (Fintype.card (CliqueFiber c.val (some i))) :=
  fun i => (b.2 i).toMatching.property.even_card

noncomputable def cliqueEvenOriginalBlocksEquiv (G : SimpleGraph V) (A : I → V → Prop) :
    (Σ c : CliqueAssignments A, CliqueOriginalBlocks G A c) ≃
      Σ c : EvenCliqueColors A, CliqueOriginalBlocks G A c.val where
  toFun d := ⟨⟨d.1,cliqueOriginalBlocks_even d.2⟩,d.2⟩
  invFun d := ⟨d.1.val,d.2⟩
  left_inv d := rfl
  right_inv d := rfl

noncomputable def cliqueEdgeBlocksEquiv (G : SimpleGraph V) (A : I → V → Prop) :
    CliqueEdgeColoredMatching G A ≃ Σ c : EvenCliqueColors A, CliqueOriginalBlocks G A c.val :=
  (cliqueEdgeDataEquiv G A).trans ((Equiv.sigmaCongrRight (cliqueOriginalBlocksEquiv G A)).trans
    (cliqueEvenOriginalBlocksEquiv G A))

end HiddenCircuits.GraphReduction
