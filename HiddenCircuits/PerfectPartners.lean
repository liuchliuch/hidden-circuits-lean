import HiddenCircuits.GraphCounting

/-! Total involutive partner functions for actual perfect matching subgraphs. -/
namespace HiddenCircuits
open SimpleGraph

/-- A total matching partner is an involution whose pairs are actual graph edges. -/
def PerfectPartner {V : Type*} (G : SimpleGraph V) :=
  {f : V → V // Function.Involutive f ∧ ∀ v, G.Adj v (f v)}

namespace PerfectPartner
variable {V : Type*} {G : SimpleGraph V}

def toSubgraph (p : PerfectPartner G) : G.Subgraph where
  verts := Set.univ
  Adj v w := p.val v = w
  adj_sub := by intro v w h; rw [← h]; exact p.property.2 v
  edge_vert := by intro v w _; trivial
  symm := by intro v w h; rw [← h]; exact p.property.1 v

 theorem toSubgraph_perfect (p : PerfectPartner G) : p.toSubgraph.IsPerfectMatching := by
  constructor
  · intro v _
    exact ⟨p.val v,rfl,fun w hw => (show p.val v = w from hw).symm⟩
  · intro v
    trivial

def toMatching (p : PerfectPartner G) : PerfectMatching G :=
  ⟨p.toSubgraph,p.toSubgraph_perfect⟩

end PerfectPartner
namespace PerfectMatching
variable {V : Type*} {G : SimpleGraph V}

/-- The unique actual partner in a perfect matching. -/
noncomputable def totalPartner (M : PerfectMatching G) (v : V) : V :=
  (M.property.1 (M.property.2 v)).choose

 theorem totalPartner_adj (M : PerfectMatching G) (v : V) : M.val.Adj v (M.totalPartner v) :=
  (M.property.1 (M.property.2 v)).choose_spec.1

 theorem totalPartner_eq_iff (M : PerfectMatching G) (v w : V) :
    M.totalPartner v = w ↔ M.val.Adj v w := by
  constructor
  · intro h
    rw [← h]
    exact M.totalPartner_adj v
  · intro h
    exact ((M.property.1 (M.property.2 v)).choose_spec.2 w h).symm

 theorem totalPartner_involutive (M : PerfectMatching G) : Function.Involutive M.totalPartner := by
  intro v
  apply (M.totalPartner_eq_iff _ _).mpr
  exact (M.totalPartner_adj v).symm

noncomputable def toPartner (M : PerfectMatching G) : PerfectPartner G :=
  ⟨M.totalPartner,M.totalPartner_involutive,fun v => M.val.adj_sub (M.totalPartner_adj v)⟩

 theorem toPartner_toMatching (M : PerfectMatching G) : M.toPartner.toMatching = M := by
  apply Subtype.ext
  apply SimpleGraph.Subgraph.ext
  · apply Set.ext
    intro v
    exact ⟨fun _ => M.property.2 v,fun _ => Set.mem_univ v⟩
  · funext v w
    exact propext (M.totalPartner_eq_iff v w)

end PerfectMatching

 theorem PerfectPartner.toMatching_toPartner {V : Type*} {G : SimpleGraph V}
    (p : PerfectPartner G) : p.toMatching.toPartner = p := by
  apply Subtype.ext
  funext v
  apply (PerfectMatching.totalPartner_eq_iff p.toMatching v (p.val v)).mpr
  rfl

/-- Exact equivalence with mathlib's actual perfect matching subgraphs. -/
noncomputable def perfectPartnerEquiv {V : Type*} (G : SimpleGraph V) :
    PerfectMatching G ≃ PerfectPartner G where
  toFun := PerfectMatching.toPartner
  invFun := PerfectPartner.toMatching
  left_inv := PerfectMatching.toPartner_toMatching
  right_inv := PerfectPartner.toMatching_toPartner

noncomputable instance {V : Type*} [Fintype V] (G : SimpleGraph V) : Fintype (PerfectPartner G) := by
  classical
  unfold PerfectPartner
  infer_instance

 theorem perfectMatchingCount_eq_partners {V : Type*} [Fintype V] (G : SimpleGraph V) :
    perfectMatchingCount G = Fintype.card (PerfectPartner G) :=
  Fintype.card_congr (perfectPartnerEquiv G)

end HiddenCircuits
