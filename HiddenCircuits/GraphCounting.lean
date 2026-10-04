import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic

/-! Canonical finite partner encodings of actual graph matchings. -/
namespace HiddenCircuits
open SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- None means unmatched; every actual partner relation is symmetric and a graph edge. -/
def EncodedMatching := {p : V → Option V //
  (∀ v w, p v = some w → p w = some v) ∧
  (∀ v w, p v = some w → G.Adj v w)}

namespace EncodedMatching
variable {G}
def toSubgraph (p : EncodedMatching G) : G.Subgraph where
  verts := {v | ∃ w, p.val v = some w}
  Adj v w := p.val v = some w
  adj_sub := fun h => p.property.2 _ _ h
  edge_vert := fun h => ⟨_,h⟩
  symm := fun v w h => p.property.1 v w h

lemma toSubgraph_isMatching (p : EncodedMatching G) : p.toSubgraph.IsMatching := by
  rintro v ⟨w,hw⟩
  refine ⟨w,hw,?_⟩
  intro y hy
  change p.val v = some y at hy
  exact Option.some.inj (Eq.trans (Eq.symm hy) hw)

lemma toSubgraph_perfect_iff (p : EncodedMatching G) :
    p.toSubgraph.IsPerfectMatching ↔ ∀ v, ∃ w, p.val v = some w := by
  constructor
  · exact fun h v => h.2 v
  · exact fun h => ⟨p.toSubgraph_isMatching,h⟩

end EncodedMatching

abbrev GraphMatching := {M : G.Subgraph // M.IsMatching}

noncomputable def GraphMatching.partner {G : SimpleGraph V} (M : GraphMatching G) (v : V) : Option V :=
  by
    classical
    exact if h : v ∈ M.val.verts then some (M.property h).choose else none

lemma GraphMatching.partner_eq_some_iff {G : SimpleGraph V} (M : GraphMatching G) (v w : V) :
    M.partner v = some w ↔ M.val.Adj v w := by
  classical
  unfold GraphMatching.partner
  split_ifs with hv
  · constructor
    · intro h
      have he := Option.some.inj h
      exact he ▸ (M.property hv).choose_spec.1
    · intro h
      congr 1
      exact ((M.property hv).choose_spec.2 w h).symm
  · simp only [false_iff]
    exact fun h => hv (M.val.edge_vert h)

noncomputable def GraphMatching.encode {G : SimpleGraph V} (M : GraphMatching G) : EncodedMatching G :=
  ⟨M.partner, by
    constructor
    · intro v w h
      exact (M.partner_eq_some_iff w v).mpr ((M.partner_eq_some_iff v w).mp h).symm
    · intro v w h
      exact M.val.adj_sub ((M.partner_eq_some_iff v w).mp h)⟩

lemma GraphMatching.encode_toSubgraph {G : SimpleGraph V} (M : GraphMatching G) :
    M.encode.toSubgraph = M.val := by
  apply SimpleGraph.Subgraph.ext
  · apply Set.ext
    intro v
    change (∃ w, M.partner v = some w) ↔ v ∈ M.val.verts
    simp_rw [M.partner_eq_some_iff]
    exact ⟨fun ⟨w,hw⟩ => M.val.edge_vert hw, fun hv => ⟨_,(M.property hv).choose_spec.1⟩⟩
  · funext v w
    exact propext (M.partner_eq_some_iff v w)

lemma EncodedMatching.toSubgraph_encode {G : SimpleGraph V} (p : EncodedMatching G) :
    (show GraphMatching G from ⟨p.toSubgraph,p.toSubgraph_isMatching⟩).encode = p := by
  apply Subtype.ext
  funext v
  apply Option.ext
  intro w
  exact (GraphMatching.partner_eq_some_iff ⟨p.toSubgraph,p.toSubgraph_isMatching⟩ v w)

/-- A bijection with mathlib's actual matching subgraphs, not a certificate assumption. -/
noncomputable def matchingEquiv (G : SimpleGraph V) : GraphMatching G ≃ EncodedMatching G where
  toFun := GraphMatching.encode
  invFun p := ⟨p.toSubgraph,p.toSubgraph_isMatching⟩
  left_inv M := Subtype.ext M.encode_toSubgraph
  right_inv := EncodedMatching.toSubgraph_encode

noncomputable instance [Fintype V] : Fintype (EncodedMatching G) := by
  classical
  unfold EncodedMatching
  infer_instance

noncomputable instance [Fintype V] : Fintype (GraphMatching G) :=
  Fintype.ofEquiv (EncodedMatching G) (matchingEquiv G).symm

/-- Partner or unmatched-marker encoding bounds all partial matchings. -/
theorem graphMatching_card_bound [Fintype V] :
    Fintype.card (GraphMatching G) ≤ (Fintype.card V + 1) ^ Fintype.card V := by
  classical
  rw [Fintype.card_congr (matchingEquiv G)]
  calc
    Fintype.card (EncodedMatching G) ≤ Fintype.card (V → Option V) := Fintype.card_le_of_injective (fun p => p.val) Subtype.val_injective
    _ = _ := by simp

/-- Perfect matchings are the actual perfect matching subgraphs. -/
abbrev PerfectMatching := {M : G.Subgraph // M.IsPerfectMatching}

def PerfectMatching.forget {G : SimpleGraph V} (M : PerfectMatching G) : GraphMatching G :=
  ⟨M.val,M.property.1⟩

lemma PerfectMatching.forget_injective {G : SimpleGraph V} :
    Function.Injective (PerfectMatching.forget (G := G)) := by
  intro M N h
  apply Subtype.ext
  exact congrArg (fun x : GraphMatching G => x.val) h

noncomputable instance [Fintype V] : Fintype (PerfectMatching G) :=
  Fintype.ofInjective PerfectMatching.forget PerfectMatching.forget_injective

noncomputable def perfectMatchingCount [Fintype V] : ℕ := Fintype.card (PerfectMatching G)

theorem perfectMatchingCount_bound [Fintype V] :
    perfectMatchingCount G ≤ (Fintype.card V + 1)^Fintype.card V :=
  (Fintype.card_le_of_injective PerfectMatching.forget PerfectMatching.forget_injective).trans
    (graphMatching_card_bound G)

/-- The partner representation loses no perfect matching and assumes no counting identity. -/
theorem encoded_perfect_correspondence (M : GraphMatching G) :
    M.val.IsPerfectMatching ↔ ∀ v, ∃ w, M.encode.val v = some w := by
  rw [← M.encode_toSubgraph]
  exact M.encode.toSubgraph_perfect_iff

end HiddenCircuits
