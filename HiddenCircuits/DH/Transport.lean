import HiddenCircuits.DH.BagMatching

/-! Graph-isomorphism transport for genuine matching boundary states. -/
namespace HiddenCircuits.DH
open SimpleGraph
open scoped BigOperators
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

def transportMatching (e : G ≃g H) (p : EncodedMatching G) : EncodedMatching H := by
  refine ⟨fun w => (p.val (e.symm w)).map e,?_,?_⟩
  · intro v w h
    cases hv : p.val (e.symm v) with
    | none => simp [hv] at h
    | some x =>
      have he : e x = w := by simpa [hv] using h
      subst w
      simp only [e.symm_apply_apply]
      rw [p.property.1 _ _ hv]
      simp
  · intro v w h
    cases hv : p.val (e.symm v) with
    | none => simp [hv] at h
    | some x =>
      have he : e x = w := by simpa [hv] using h
      subst w
      have ha : H.Adj (e (e.symm v)) (e x) := e.map_rel_iff.mpr (p.property.2 _ _ hv)
      simpa using ha

lemma transportMatching_symm (e : G ≃g H) (p : EncodedMatching G) :
    transportMatching e.symm (transportMatching e p) = p := by
  apply Subtype.ext
  funext v
  change Option.map e.symm (Option.map e (p.val (e.symm (e v)))) = p.val v
  simp

/-- Relabeling actual graphs gives a bijection, without any assumed cardinal identity. -/
def transportMatchingEquiv (e : G ≃g H) : EncodedMatching G ≃ EncodedMatching H where
  toFun := transportMatching e
  invFun := transportMatching e.symm
  left_inv := transportMatching_symm e
  right_inv := transportMatching_symm e.symm

lemma transport_admissible_iff (e : G ≃g H) (T : Set V) (p : EncodedMatching G) :
    Admissible (e '' T) (transportMatching e p) ↔ Admissible T p := by
  constructor
  · intro h v hv
    have he : (transportMatching e p).val (e v)=none := by simp [transportMatching,hv]
    obtain ⟨u,hu,hue⟩ := h (e v) he
    exact e.injective hue ▸ hu
  · intro h w hw
    have he : p.val (e.symm w)=none := by simpa [transportMatching] using hw
    exact ⟨e.symm w,h _ he,by simp⟩

lemma transport_uncovered [Fintype V] [Fintype W] (e : G ≃g H) (p : EncodedMatching G) :
    uncovered (transportMatching e p) = uncovered p := by
  classical
  unfold uncovered
  rw [← e.toEquiv.sum_comp]
  simp [transportMatching]

noncomputable def transportBagStateEquiv [Fintype V] [Fintype W]
    (e : G ≃g H) (T : Set V) (k : ℕ) : BagState G T k ≃ BagState H (e '' T) k :=
  (transportMatchingEquiv e).subtypeEquiv (by
    intro p
    change (Admissible T p ∧ uncovered p = k) ↔
      Admissible (e '' T) (transportMatching e p) ∧ uncovered (transportMatching e p) = k
    rw [transport_admissible_iff,transport_uncovered])

theorem transport_bag_count [Fintype V] [Fintype W]
    (e : G ≃g H) (T : Set V) (k : ℕ) :
    Fintype.card (BagState G T k) = Fintype.card (BagState H (e '' T) k) :=
  Fintype.card_congr (transportBagStateEquiv e T k)

end HiddenCircuits.DH
