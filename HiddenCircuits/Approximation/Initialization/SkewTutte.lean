import HiddenCircuits.Approximation.Initialization.SkewLinear
import HiddenCircuits.PerfectPartners
import Mathlib.Combinatorics.SimpleGraph.Tutte

/-! A nonsingular skew matrix supported on the edges of a finite
graph certifies a genuine perfect matching. Tutte's theorem is instantiated
using odd-component kernel vectors and a finite-dimensional rank bound. -/
namespace HiddenCircuits.Approximation.Initialization.SkewTutte
open scoped BigOperators Matrix
open Matrix SimpleGraph

noncomputable def extend {I V : Type*} (e : I ↪ V) (x : I → ℚ) : V → ℚ :=
  Function.extend e x 0

@[simp] theorem extend_at {I V : Type*} (e : I ↪ V) (x : I → ℚ) (i : I) :
    extend e x (e i) = x i := e.injective.extend_apply x 0 i

theorem extend_off {I V : Type*} (e : I ↪ V) (x : I → ℚ) (i : V)
    (h : i ∉ Set.range e) : extend e x i = 0 :=
  Function.extend_apply' x (0 : V → ℚ) i h

theorem mulVec_extend {I V : Type*} [Fintype I] [Fintype V]
    (e : I ↪ V) (x : I → ℚ) (A : Matrix V V ℚ) (i : V) :
    (A *ᵥ extend e x) i = ∑ j, A i (e j) * x j := by
  classical
  symm
  apply Fintype.sum_of_injective e e.injective
  · intro j hj
    simp [extend_off e x j hj]
  · intro j
    simp

abbrev deleted {V : Type*} (G : SimpleGraph V) (S : Set V) :=
  ((⊤ : G.Subgraph).deleteVerts S).coe

def componentEmbedding {V : Type*} (G : SimpleGraph V) (S : Set V)
    (c : (deleted G S).ConnectedComponent) : c.supp ↪ V where
  toFun x := x.val.val
  inj' := by
    intro i j h
    apply Subtype.ext
    exact Subtype.ext h

theorem component_disjoint {V : Type*} (G : SimpleGraph V) (S : Set V)
    (c d : (deleted G S).ConnectedComponent) (hcd : c ≠ d)
    (i : c.supp) : componentEmbedding G S c i ∉ Set.range (componentEmbedding G S d) := by
  rintro ⟨j, hj⟩
  have he : j.val = i.val := Subtype.ext hj
  exact hcd (ConnectedComponent.eq_of_common_vertex i.property (he ▸ j.property))

theorem component_mulVec_zero {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Set V) (A : Matrix V V ℚ)
    (hsupport : ∀ i j, ¬G.Adj i j → A i j = 0)
    (c : (deleted G S).ConnectedComponent) [Fintype c.supp]
    (x : c.supp → ℚ)
    (hx : (A.submatrix (componentEmbedding G S c) (componentEmbedding G S c)) *ᵥ x = 0)
    (i : V) (hi : i ∉ S) :
    (A *ᵥ extend (componentEmbedding G S c) x) i = 0 := by
  classical
  rw [mulVec_extend]
  by_cases hm : i ∈ Set.range (componentEmbedding G S c)
  · obtain ⟨j, rfl⟩ := hm
    exact congrFun hx j
  · apply Finset.sum_eq_zero
    intro j _
    have he : ¬G.Adj i (componentEmbedding G S c j) := by
      intro ha
      let u : ((⊤ : G.Subgraph).deleteVerts S).verts := ⟨i, ⟨Set.mem_univ i, hi⟩⟩
      have huj : (deleted G S).Adj u j.val := by
        apply Subgraph.deleteVerts_adj.mpr
        exact ⟨Set.mem_univ i, hi, Set.mem_univ _, j.val.property.2, ha⟩
      have hu : u ∈ c.supp := (c.mem_supp_congr_adj huj).mpr j.property
      exact hm ⟨⟨u, hu⟩, rfl⟩
    rw [hsupport i _ he, zero_mul]

theorem perfectMatching_of_det_ne_zero {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : Matrix V V ℚ)
    (hskew : A.transpose = -A)
    (hsupport : ∀ i j, ¬G.Adj i j → A i j = 0)
    (hdet : A.det ≠ 0) : Nonempty (PerfectMatching G) := by
  classical
  apply (show Nonempty (PerfectMatching G) ↔ ∃ M : G.Subgraph, M.IsPerfectMatching from
    ⟨fun ⟨M⟩ => ⟨M.val, M.property⟩, fun ⟨M, hM⟩ => ⟨⟨M, hM⟩⟩⟩).mpr
  apply SimpleGraph.tutte.mpr
  intro S hS
  let C := (deleted G S).oddComponents
  letI : Fintype C := Fintype.ofFinite C
  letI (c : C) : Fintype c.val.supp := Fintype.ofFinite c.val.supp
  have kernels : ∀ c : C, ∃ x : c.val.supp → ℚ, x ≠ 0 ∧
      (A.submatrix (componentEmbedding G S c.val) (componentEmbedding G S c.val)) *ᵥ x = 0 := by
    intro c
    apply SkewLinear.odd_kernel
    · ext i j
      exact congrFun (congrFun hskew (componentEmbedding G S c.val i))
        (componentEmbedding G S c.val j)
    · rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
      exact c.property
  choose x hx hkernel using kernels
  let v : C → V → ℚ := fun c => extend (componentEmbedding G S c.val) (x c)
  have hi : LinearIndependent ℚ v := by
    apply SkewLinear.independent_of_separating_coordinates
    intro c
    obtain ⟨i, hi⟩ : ∃ i, x c i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx c (funext h)
    refine ⟨componentEmbedding G S c.val i, ?_, ?_⟩
    · simpa [v] using hi
    · intro d hdc
      apply extend_off
      exact component_disjoint G S c.val d.val
        (fun h => hdc (Subtype.ext h.symm)) i
  have hz : ∀ c i, i ∉ S → (A *ᵥ v c) i = 0 := by
    intro c i hi
    exact component_mulVec_zero G S A hsupport c.val (x c) (hkernel c) i hi
  have hbound := SkewLinear.independent_count_le_coordinates A hdet S v hi hz
  have hc : Fintype.card C = (deleted G S).oddComponents.ncard := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  rw [hc, Nat.card_coe_set_eq] at hbound
  exact (not_lt_of_ge hbound) hS

end HiddenCircuits.Approximation.Initialization.SkewTutte
