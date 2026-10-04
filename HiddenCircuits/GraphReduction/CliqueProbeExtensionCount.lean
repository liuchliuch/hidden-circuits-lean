import HiddenCircuits.GraphReduction.CliqueProbeExtension

/-! Cardinal and parity consequences of the genuine clique-extension bijection. -/
namespace HiddenCircuits.GraphReduction
variable {X P : Type*} [Fintype X] [Fintype P]

noncomputable instance cliqueRemainderFintype (f : X ↪ P) : Fintype (CliqueRemainder f) := by
  classical
  unfold CliqueRemainder
  infer_instance

 theorem cliqueRemainder_card (f : X ↪ P) :
    Fintype.card (CliqueRemainder f)=Fintype.card P-Fintype.card X := by
  have h := Fintype.card_congr (injectionPartition f)
  rw [Fintype.card_sum] at h
  omega

/-- Actual clique-probe extensions are counted by actual residual clique matchings. -/
theorem cliqueExtension_card_sum :
    Fintype.card (CliqueExtension X P) =
      ∑ f : X ↪ P, Fintype.card (PerfectPartner (⊤ : SimpleGraph (CliqueRemainder f))) := by
  classical
  rw [Fintype.card_congr (cliqueExtensionEquiv (X:=X) (P:=P)),Fintype.card_sigma]

/-- An even probe class forces the number of attached original vertices to be even. -/
theorem cliqueExtension_even (p : CliqueExtension X P) (hP : Even (Fintype.card P)) :
    Even (Fintype.card X) := by
  have h := p.toMatching.property.even_card
  simp only [Fintype.card_sum] at h
  obtain ⟨a,ha⟩ := h
  obtain ⟨b,hb⟩ := hP
  refine ⟨Fintype.card X/2,?_⟩
  omega

/-- Too few probe labels make every purported extension impossible. -/
theorem cliqueExtension_card_insufficient (h : Fintype.card P<Fintype.card X) :
    Fintype.card (CliqueExtension X P)=0 := by
  letI : IsEmpty (CliqueExtension X P) := ⟨fun p =>
    (not_le_of_gt h) (Fintype.card_le_of_embedding p.injection)⟩
  exact Fintype.card_eq_zero

end HiddenCircuits.GraphReduction
