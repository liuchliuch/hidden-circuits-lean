import HiddenCircuits.Complexity.GraphEncoding
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Vertex cloning converts positive integer activities to ordinary unweighted
independent-set counts by an actual bijection. -/
namespace HiddenCircuits.Complexity.Cloning
open scoped BigOperators
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

abbrev IndependentSet := {s : Set V // G.IsIndepSet s}
noncomputable instance : Fintype (IndependentSet G) := by
  classical
  unfold IndependentSet
  infer_instance

noncomputable instance independentVertices (s : IndependentSet G) : Fintype s.val :=
  Fintype.ofFinite s.val

abbrev Vertex (r : V → ℕ) := (v : V) × Fin (r v)

/-- Every vertex is replaced by a clique of its requested number of copies;
base edges are replaced by complete joins between the corresponding cliques. -/
def graph (r : V → ℕ) : SimpleGraph (Vertex r) where
  Adj u v := (u.1 = v.1 ∧ u ≠ v) ∨ G.Adj u.1 v.1
  symm := by
    intro u v h
    exact h.elim (fun h => Or.inl ⟨h.1.symm,Ne.symm h.2⟩) (fun h => Or.inr h.symm)
  loopless := ⟨by intro u; simp⟩

noncomputable instance (r : V → ℕ) : Fintype (IndependentSet (graph G r)) := by
  classical
  unfold IndependentSet
  infer_instance

/-- An independent base set with one chosen clone for each selected vertex. -/
abbrev ColoredSet (r : V → ℕ) := (s : IndependentSet G) × ((v : s.val) → Fin (r v.val))

noncomputable instance (r : V → ℕ) : Fintype (ColoredSet G r) := by
  classical
  unfold ColoredSet
  infer_instance

variable {G} {r : V → ℕ}

def project (s : IndependentSet (graph G r)) : IndependentSet G :=
  ⟨{v | ∃ i : Fin (r v), (⟨v,i⟩ : Vertex r) ∈ s.val}, by
    intro v hv w hw hne hG
    obtain ⟨i,hi⟩ := hv
    obtain ⟨j,hj⟩ := hw
    apply s.property hi hj (fun he => hne (congrArg Sigma.fst he))
    exact Or.inr hG⟩

lemma fiber_unique (s : IndependentSet (graph G r)) {v : V} {i j : Fin (r v)}
    (hi : (⟨v,i⟩ : Vertex r) ∈ s.val) (hj : (⟨v,j⟩ : Vertex r) ∈ s.val) : i = j := by
  by_contra h
  have hne : (⟨v,i⟩ : Vertex r) ≠ ⟨v,j⟩ := by simpa using h
  exact s.property hi hj hne (Or.inl ⟨rfl,hne⟩)

noncomputable def color (s : IndependentSet (graph G r)) (v : (project s).val) : Fin (r v.val) :=
  v.property.choose

lemma color_mem (s : IndependentSet (graph G r)) (v : (project s).val) :
    (⟨v.val,color s v⟩ : Vertex r) ∈ s.val := v.property.choose_spec

noncomputable def decode (s : IndependentSet (graph G r)) : ColoredSet G r :=
  ⟨project s,color s⟩

def encode (s : ColoredSet G r) : IndependentSet (graph G r) :=
  ⟨{u | ∃ h : u.1 ∈ s.1.val, s.2 ⟨u.1,h⟩ = u.2}, by
    intro u hu v hv hne hadj
    obtain ⟨hu,hcu⟩ := hu
    obtain ⟨hv,hcv⟩ := hv
    rcases hadj with ⟨he,hne'⟩ | he
    · cases u with
      | mk u i =>
        cases v with
        | mk v j =>
          dsimp at he
          subst v
          have hij : i = j := hcu.symm.trans hcv
          exact hne' (by cases hij; rfl)
    · by_cases huv : u.1 = v.1
      · exact G.loopless.irrefl u.1 (huv ▸ he)
      · exact s.1.property hu hv huv he⟩

lemma encode_decode (s : IndependentSet (graph G r)) : encode (decode s) = s := by
  apply Subtype.ext
  ext u
  constructor
  · rintro ⟨h,hc⟩
    have hm := color_mem s ⟨u.1,h⟩
    change color s ⟨u.1,h⟩ = u.2 at hc
    simpa only [hc] using hm
  · intro h
    have hp : u.1 ∈ (project s).val := ⟨u.2,h⟩
    refine ⟨hp,?_⟩
    exact fiber_unique s (color_mem s ⟨u.1,hp⟩) h

lemma encode_injective : Function.Injective (encode (G := G) (r := r)) := by
  intro s t h
  have hs : s.1 = t.1 := by
    apply Subtype.ext
    ext v
    constructor
    · intro hv
      have hm : (⟨v,s.2 ⟨v,hv⟩⟩ : Vertex r) ∈ (encode s).val := ⟨hv,rfl⟩
      rw [h] at hm
      exact hm.choose
    · intro hv
      have hm : (⟨v,t.2 ⟨v,hv⟩⟩ : Vertex r) ∈ (encode t).val := ⟨hv,rfl⟩
      rw [← h] at hm
      exact hm.choose
  cases s with
  | mk s f =>
    cases t with
    | mk t g =>
      dsimp at hs
      subst t
      have hfg : f = g := by
        funext v
        have hm : (⟨v.val,f v⟩ : Vertex r) ∈ (encode ⟨s,f⟩).val := ⟨v.property,rfl⟩
        rw [h] at hm
        exact hm.choose_spec.symm
      cases hfg
      rfl

/-- No independent set is lost and no clone multiplicity is silently divided out. -/
noncomputable def independentEquiv : ColoredSet G r ≃ IndependentSet (graph G r) :=
  Equiv.ofBijective encode ⟨encode_injective,fun s => ⟨decode s,encode_decode s⟩⟩

/-- The unweighted clone count equals the independence generating sum at the
integer activities `r v`. -/
theorem independent_count :
    Fintype.card (IndependentSet (graph G r)) =
      ∑ s : IndependentSet G, ∏ v : s.val, r v.val := by
  rw [← Fintype.card_congr (independentEquiv (G := G) (r := r))]
  simp [ColoredSet,Fintype.card_sigma,Fintype.card_pi]

/-- Exact number of vertices emitted by cloning. -/
theorem vertex_count : Fintype.card (Vertex r) = ∑ v, r v := by
  simp [Vertex,Fintype.card_sigma]

end HiddenCircuits.Complexity.Cloning
