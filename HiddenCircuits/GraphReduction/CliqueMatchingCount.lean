import HiddenCircuits.GraphReduction.CliqueProbeExtension

/-! Count actual perfect matchings of a complete graph by removing one forced pair. -/
namespace HiddenCircuits.GraphReduction
open scoped BigOperators

noncomputable def cliquePartnerCount (n : ℕ) : ℕ :=
  Fintype.card (PerfectPartner (⊤ : SimpleGraph (Fin n)))

/-- The number of complete-graph partners depends only on the number of labels. -/
theorem completePartner_card {V : Type*} [Fintype V] (n : ℕ) (h : Fintype.card V=n) :
    Fintype.card (PerfectPartner (⊤ : SimpleGraph V))=cliquePartnerCount n := by
  classical
  let e : V ≃ Fin n := Fintype.equivOfCardEq (h.trans (Fintype.card_fin n).symm)
  exact Fintype.card_congr (perfectPartnerCongr _ _ e (by
    intro v w
    simp only [SimpleGraph.top_adj,e.injective.ne_iff]))

 theorem singletonExtension_top (P : Type*) : cliqueExtensionGraph Unit P=⊤ := by
  ext x y
  cases x with
  | inl x => cases y with
    | inl y => simp [cliqueExtensionGraph,SimpleGraph.top_adj,Subsingleton.elim x y]
    | inr y => simp [cliqueExtensionGraph,SimpleGraph.top_adj]
  | inr x => cases y with
    | inl y => simp [cliqueExtensionGraph,SimpleGraph.top_adj]
    | inr y => simp [cliqueExtensionGraph,SimpleGraph.top_adj]

/-- There is exactly one empty matching. -/
@[simp] theorem cliquePartnerCount_zero : cliquePartnerCount 0=1 := by
  apply Fintype.card_eq_one_iff.mpr
  refine ⟨⟨id,fun v => rfl,fun v => Fin.elim0 v⟩,?_⟩
  intro p
  apply Subtype.ext
  funext v
  exact Fin.elim0 v

/-- Removing the partner of a distinguished vertex gives the literal n+1 choices
and a complete matching on the remaining n vertices. -/
theorem cliquePartnerCount_add_two (n : ℕ) :
    cliquePartnerCount (n+2)=(n+1)*cliquePartnerCount n := by
  classical
  letI (f : Unit ↪ Fin (n+1)) : Fintype (CliqueRemainder f) := by
    unfold CliqueRemainder
    infer_instance
  have hc : Fintype.card (Unit ⊕ Fin (n+1))=n+2 := by simp; omega
  rw [← completePartner_card (V := Unit ⊕ Fin (n+1)) (n+2) hc]
  rw [← singletonExtension_top]
  change Fintype.card (CliqueExtension Unit (Fin (n+1)))=_
  rw [Fintype.card_congr (cliqueExtensionEquiv (X := Unit) (P := Fin (n+1))),Fintype.card_sigma]
  have hr (f : Unit ↪ Fin (n+1)) : Fintype.card (CliqueRemainder f)=n := by
    have he := Fintype.card_congr (injectionPartition f)
    simp only [Fintype.card_sum,Fintype.card_unit,Fintype.card_fin] at he
    omega
  simp_rw [completePartner_card n (hr _)]
  rw [Finset.sum_const,Finset.card_univ,Fintype.card_embedding_eq_of_unique]
  simp [Nat.nsmul_eq_mul]

/-- The odd factorial, with the empty product convention at zero. -/
def oddFactorial (a : ℕ) : ℕ := ∏ j ∈ Finset.range a, (2*j+1)

@[simp] theorem oddFactorial_zero : oddFactorial 0=1 := by simp [oddFactorial]
@[simp] theorem oddFactorial_succ (a : ℕ) : oddFactorial (a+1)=(2*a+1)*oddFactorial a := by
  simp [oddFactorial,Finset.prod_range_succ,Nat.mul_comm]

 theorem cliquePartnerCount_even (a : ℕ) : cliquePartnerCount (2*a)=oddFactorial a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [show 2*(a+1)=2*a+2 by omega,cliquePartnerCount_add_two,ih,oddFactorial_succ]

/-- Complete-graph counting for arbitrary finite residual types in clique probes. -/
theorem completePartner_card_even {V : Type*} [Fintype V] (a : ℕ) (h : Fintype.card V=2*a) :
    Fintype.card (PerfectPartner (⊤ : SimpleGraph V))=oddFactorial a := by
  rw [completePartner_card (2*a) h,cliquePartnerCount_even]

 theorem completeMatchingCount_even {V : Type*} [Fintype V] (a : ℕ) (h : Fintype.card V=2*a) :
    perfectMatchingCount (⊤ : SimpleGraph V)=oddFactorial a := by
  rw [perfectMatchingCount_eq_partners,completePartner_card_even a h]

end HiddenCircuits.GraphReduction
