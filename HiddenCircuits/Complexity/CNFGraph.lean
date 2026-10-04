import HiddenCircuits.Complexity.GraphEncoding
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Arbitrary-CNF clause graph and exact cancellation

No 3-CNF splitting is used: ordinary clause splitting is not parsimonious.
The graph has one true/false pair per variable and one vertex per clause.
A clause vertex is joined precisely to the literals satisfying that clause.
-/
namespace HiddenCircuits.Complexity
open scoped BigOperators

structure CNF (n m : ℕ) where
  clause : Fin m → List (Fin n × Bool)

namespace CNF
variable {n m : ℕ} (F : CNF n m)

abbrev Assignment := Fin n → Bool
abbrev Vertex := (Fin n × Bool) ⊕ Fin m

def ClauseSatisfied (w : Assignment (n := n)) (k : Fin m) : Prop :=
  ∃ b ∈ F.clause k, w b.1 = b.2

instance (w : Assignment (n := n)) (k : Fin m) : Decidable (F.ClauseSatisfied w k) :=
  inferInstanceAs (Decidable (∃ b ∈ F.clause k, w b.1 = b.2))

def Satisfies (w : Assignment (n := n)) : Prop := ∀ k, F.ClauseSatisfied w k
instance (w : Assignment (n := n)) : Decidable (F.Satisfies w) :=
  inferInstanceAs (Decidable (∀ k, F.ClauseSatisfied w k))

noncomputable def satCount : ℕ := Fintype.card {w : Assignment (n := n) // F.Satisfies w}

/-- The actual simple graph used in the weighted source reduction. -/
def graph : SimpleGraph (Vertex (n := n) (m := m)) where
  Adj
    | .inl (i,b), .inl (j,c) => i = j ∧ b ≠ c
    | .inl a, .inr k => a ∈ F.clause k
    | .inr k, .inl a => a ∈ F.clause k
    | .inr _, .inr _ => False
  symm := by
    intro v w h
    cases v with
    | inl a => cases w with
      | inl b => exact ⟨h.1.symm,Ne.symm h.2⟩
      | inr b => exact h
    | inr a => cases w with
      | inl b => exact h
      | inr b => exact h
  loopless := ⟨by intro v; cases v <;> simp⟩

instance : DecidableRel F.graph.Adj := by
  intro v w
  cases v <;> cases w <;> dsimp [graph] <;> infer_instance

/-- Choosing all `n` variable vertices fixes a unique assignment. -/
def selected (w : Assignment (n := n)) (c : Fin m → Bool) : Set (Vertex (n := n) (m := m))
  | .inl (i,b) => b = w i
  | .inr k => c k = true

@[simp] lemma mem_selected_inr (w : Assignment (n := n)) (c : Fin m → Bool) (k : Fin m) :
    Sum.inr k ∈ selected w c ↔ c k = true := Iff.rfl

@[simp] lemma mem_selected_inl (w : Assignment (n := n)) (c : Fin m → Bool)
    (i : Fin n) (b : Bool) : Sum.inl (i,b) ∈ selected w c ↔ b = w i := Iff.rfl

/-- Selected clause vertices must be unsatisfied by the selected variable vertices. -/
def Compatible (w : Assignment (n := n)) (c : Fin m → Bool) : Prop :=
  ∀ k, c k = true → ¬ F.ClauseSatisfied w k

instance (w : Assignment (n := n)) (c : Fin m → Bool) : Decidable (F.Compatible w c) :=
  inferInstanceAs (Decidable (∀ k, c k = true → ¬ F.ClauseSatisfied w k))

theorem selected_independent_iff (w : Assignment (n := n)) (c : Fin m → Bool) :
    F.graph.IsIndepSet (selected w c) ↔ F.Compatible w c := by
  constructor
  · intro h k hk ⟨⟨i,b⟩,hb,hw⟩
    exact h (x := Sum.inl (i,b)) (y := Sum.inr k) hw.symm hk (by simp) hb
  · intro h v hv u hu hne hadj
    cases v with
    | inl a =>
      rcases a with ⟨i,b⟩
      cases u with
      | inl a =>
        rcases a with ⟨j,d⟩
        obtain ⟨hij,hbd⟩ := hadj
        subst j
        exact hbd (hv.trans hu.symm)
      | inr k => exact h k hu ⟨(i,b),hadj,hv.symm⟩
    | inr k =>
      cases u with
      | inl a => exact h k hv ⟨a,hadj,hu.symm⟩
      | inr j => exact hadj

/-- Actual independent vertex sets that choose exactly one literal per variable. -/
abbrev FullIndependentSet :=
  {s : Set (Vertex (n := n) (m := m)) // F.graph.IsIndepSet s ∧
    ∀ i : Fin n, ∃! b : Bool, Sum.inl (i,b) ∈ s}

abbrev FullChoice :=
  {wc : Assignment (n := n) × (Fin m → Bool) // F.Compatible wc.1 wc.2}

noncomputable instance : Fintype F.FullIndependentSet := by
  classical
  unfold FullIndependentSet
  infer_instance

noncomputable instance : Fintype F.FullChoice := by
  classical
  unfold FullChoice
  infer_instance

def choiceToSet (wc : F.FullChoice) : F.FullIndependentSet :=
  ⟨selected wc.val.1 wc.val.2, (F.selected_independent_iff _ _).mpr wc.property,
    fun i => ⟨wc.val.1 i, rfl, fun _ h => h⟩⟩

theorem choiceToSet_injective : Function.Injective F.choiceToSet := by
  intro x y h
  have hs : selected x.val.1 x.val.2 = selected y.val.1 y.val.2 := congrArg Subtype.val h
  apply Subtype.ext
  apply Prod.ext
  · funext i
    have hi := Set.ext_iff.mp hs (Sum.inl (i,x.val.1 i))
    exact hi.mp rfl
  · funext k
    have hk := Set.ext_iff.mp hs (Sum.inr k)
    change (x.val.2 k = true ↔ y.val.2 k = true) at hk
    cases hx : x.val.2 k <;> cases hy : y.val.2 k <;> simp_all

noncomputable def setAssignment (s : F.FullIndependentSet) : Assignment (n := n) :=
  fun i => (s.property.2 i).choose

lemma setAssignment_mem_iff (s : F.FullIndependentSet) (i : Fin n) (b : Bool) :
    Sum.inl (i,b) ∈ s.val ↔ b = F.setAssignment s i := by
  constructor
  · exact (s.property.2 i).choose_spec.2 b
  · rintro rfl
    exact (s.property.2 i).choose_spec.1

noncomputable def setClauseMask (s : F.FullIndependentSet) : Fin m → Bool := by
  classical
  exact fun k => decide (Sum.inr k ∈ s.val)

lemma selected_decoded (s : F.FullIndependentSet) :
    selected (F.setAssignment s) (F.setClauseMask s) = s.val := by
  classical
  ext v
  cases v with
  | inl a => exact (F.setAssignment_mem_iff s a.1 a.2).symm
  | inr k =>
    change decide (Sum.inr k ∈ s.val) = true ↔ Sum.inr k ∈ s.val
    simp

theorem choiceToSet_surjective : Function.Surjective F.choiceToSet := by
  intro s
  have hc : F.Compatible (F.setAssignment s) (F.setClauseMask s) := by
    apply (F.selected_independent_iff _ _).mp
    rw [F.selected_decoded s]
    exact s.property.1
  refine ⟨⟨(F.setAssignment s,F.setClauseMask s),hc⟩,?_⟩
  exact Subtype.ext (F.selected_decoded s)

/-- Exact graph/assignment correspondence. In particular, a satisfying assignment
has exactly one extension when no clause vertices are selected. -/
noncomputable def fullChoiceEquiv : F.FullChoice ≃ F.FullIndependentSet :=
  Equiv.ofBijective F.choiceToSet ⟨F.choiceToSet_injective,F.choiceToSet_surjective⟩

/-- The graph has exactly `2n+m` vertices, including empty formulas/clauses. -/
theorem graph_vertex_count : Fintype.card (Vertex (n := n) (m := m)) = 2*n+m := by
  simp [Vertex]
  omega

/-- For a fixed assignment, summing over all clause-vertex choices factorizes.
A satisfied clause cannot be selected; an unsatisfied clause contributes `1+y`. -/
theorem clause_activity_factorization (w : Assignment (n := n)) (y : ℤ) :
    (∑ c : Fin m → Bool, ∏ k,
      if c k then (if F.ClauseSatisfied w k then 0 else y) else 1) =
    ∏ k, (1 + if F.ClauseSatisfied w k then 0 else y) := by
  calc
    _ = ∏ k, ∑ b : Bool, (if b then (if F.ClauseSatisfied w k then (0 : ℤ) else y) else 1) :=
      (Fintype.prod_sum (fun (k : Fin m) (b : Bool) =>
        if b then (if F.ClauseSatisfied w k then (0 : ℤ) else y) else 1)).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro k _
      rw [Fintype.sum_bool]
      simp only [Bool.false_eq_true, if_false, if_true]
      omega

/-- At activity `-1`, precisely the satisfying assignments survive; every
unsatisfied clause cancels its present/absent alternatives exactly. -/
theorem clause_activity_minus_one (w : Assignment (n := n)) :
    (∑ c : Fin m → Bool, ∏ k,
      if c k then (if F.ClauseSatisfied w k then (0 : ℤ) else -1) else 1) =
    if F.Satisfies w then 1 else 0 := by
  rw [F.clause_activity_factorization]
  by_cases h : F.Satisfies w
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro k _
    simp [h k]
  · rw [if_neg h]
    obtain ⟨k,hk⟩ := not_forall.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    simp [hk]

/-- Exact signed recovery of #SAT from the clause-choice weights. This is a
counting identity, not merely equisatisfiability. -/
theorem satCount_signed_recovery :
    (F.satCount : ℤ) =
    ∑ w : Assignment (n := n), ∑ c : Fin m → Bool, ∏ k,
      if c k then (if F.ClauseSatisfied w k then (0 : ℤ) else -1) else 1 := by
  simp_rw [F.clause_activity_minus_one]
  simp [satCount, Fintype.card_subtype]

/-- Each incompatible mask has weight zero; compatible masks carry the sign of
exactly the selected clause vertices. -/
theorem clause_weight_eq (w : Assignment (n := n)) (c : Fin m → Bool) :
    (∏ k, if c k then (if F.ClauseSatisfied w k then (0 : ℤ) else -1) else 1) =
    if F.Compatible w c then (∏ k, if c k then (-1 : ℤ) else 1) else 0 := by
  by_cases h : F.Compatible w c
  · rw [if_pos h]
    apply Finset.prod_congr rfl
    intro k _
    by_cases hc : c k = true
    · simp [hc,h k hc]
    · simp [hc]
  · rw [if_neg h]
    simp only [Compatible, not_forall, Classical.not_imp, not_not] at h
    obtain ⟨k,hc,hk⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    simp [hc,hk]

/-- Sign-weighted sum over actual independent vertex sets containing exactly
one true/false vertex for each variable. -/
noncomputable def signedFullIndependentCount : ℤ := by
  classical
  exact ∑ s : F.FullIndependentSet, ∏ k : Fin m,
    if Sum.inr k ∈ s.val then (-1 : ℤ) else 1

/-- The weighted arbitrary-CNF graph recovers the exact number of satisfying
assignments. The independent sets and cancellation are both concrete. -/
theorem satCount_eq_signedFullIndependentCount :
    (F.satCount : ℤ) = F.signedFullIndependentCount := by
  classical
  rw [F.satCount_signed_recovery]
  simp_rw [F.clause_weight_eq]
  rw [← Fintype.sum_prod_type (fun wc : Assignment (n := n) × (Fin m → Bool) =>
    if F.Compatible wc.1 wc.2 then (∏ k, if wc.2 k then (-1 : ℤ) else 1) else 0)]
  let weight : Assignment (n := n) × (Fin m → Bool) → ℤ :=
    fun wc => ∏ k, if wc.2 k then -1 else 1
  have hs : (∑ wc : F.FullChoice, weight wc.val) =
      ∑ wc : Assignment (n := n) × (Fin m → Bool),
        if F.Compatible wc.1 wc.2 then weight wc else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype _ (by simp) weight).symm
  rw [← hs]
  change (∑ wc : F.FullChoice, weight wc.val) =
    ∑ s : F.FullIndependentSet, ∏ k : Fin m, if Sum.inr k ∈ s.val then (-1 : ℤ) else 1
  convert Fintype.sum_equiv F.fullChoiceEquiv
    (fun wc => weight wc.val)
    (fun s => ∏ k : Fin m, if Sum.inr k ∈ s.val then (-1 : ℤ) else 1) ?_
  intro wc
  simp [fullChoiceEquiv,choiceToSet,weight]

end CNF
end HiddenCircuits.Complexity
