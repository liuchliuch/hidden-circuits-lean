import HiddenCircuits.PairedTransfers

namespace HiddenCircuits
open scoped BigOperators

namespace State
 theorem weight_finset {n q : ℕ} (S : State n q) : S.weight = ∑ x ∈ S.val, x.val := by
  rw [← S.image_track,Finset.sum_image (fun _ _ _ _ h => S.track.injective h)]
  rfl

 theorem halfComplement_weight_add {p : ℕ} (S : State (2*p) p) :
    S.weight+S.halfComplement.weight = ∑ x : Fin (2*p), x.val := by
  rw [weight_finset,weight_finset,halfComplement_val]
  exact Finset.sum_add_sum_compl S.val _
end State

 theorem dualUpper_weight_le {p : ℕ} (S T : State (2*p) p)
    (h : halfDual (compound (upper (2*p))) S T ≠ 0) : S.weight ≤ T.weight := by
  have hh := compound_upper_weight_le T.halfComplement S.halfComplement h
  have hs := S.halfComplement_weight_add
  have ht := T.halfComplement_weight_add
  omega

 theorem dualUpper_eq_states {p : ℕ} (S T : State (2*p) p)
    (h : halfDual (compound (upper (2*p))) S T ≠ 0) (he : S.weight=T.weight) : S=T := by
  have hs := S.halfComplement_weight_add
  have ht := T.halfComplement_weight_add
  have hh := compound_upper_eq_states T.halfComplement S.halfComplement h (by omega)
  exact ((State.halfComplement_injective p) hh).symm

@[simp] theorem dualUpper_self {p : ℕ} (S : State (2*p) p) :
    halfDual (compound (upper (2*p))) S S=1 := compound_upper_self _

 theorem pairedBackground_weight_le {p : ℕ} (S T : State (2*p) p)
    (h : pairedBackground p S T ≠ 0) : S.weight≤T.weight := by
  rw [pairedBackground,pairedTransfer_transpose,Matrix.mul_apply] at h
  obtain ⟨U,_,hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have h1 := compound_upper_weight_le S U (fun hz => hu (by rw [hz,zero_mul]))
  have h2 := dualUpper_weight_le U T (fun hz => hu (by rw [hz,mul_zero]))
  omega

 theorem pairedBackground_eq_states {p : ℕ} (S T : State (2*p) p)
    (h : pairedBackground p S T ≠ 0) (he : S.weight=T.weight) : S=T := by
  rw [pairedBackground,pairedTransfer_transpose,Matrix.mul_apply] at h
  obtain ⟨U,_,hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hF : compound (upper (2*p)) S U ≠ 0 := fun hz => hu (by rw [hz,zero_mul])
  have hD : halfDual (compound (upper (2*p))) U T ≠ 0 := fun hz => hu (by rw [hz,mul_zero])
  have h1 := compound_upper_weight_le S U hF
  have h2 := dualUpper_weight_le U T hD
  exact (compound_upper_eq_states S U hF (by omega)).trans (dualUpper_eq_states U T hD (by omega))

@[simp] theorem pairedBackground_self {p : ℕ} (S : State (2*p) p) : pairedBackground p S S=1 := by
  rw [pairedBackground,pairedTransfer_transpose,Matrix.mul_apply,Finset.sum_eq_single S]
  · simp
  · intro U _ hU
    by_contra hn
    have hF : compound (upper (2*p)) S U ≠ 0 := fun hz => hn (by rw [hz,zero_mul])
    have hD : halfDual (compound (upper (2*p))) U S ≠ 0 := fun hz => hn (by rw [hz,mul_zero])
    have h1 := compound_upper_weight_le S U hF
    have h2 := dualUpper_weight_le U S hD
    exact hU (compound_upper_eq_states S U hF (by omega)).symm
  · simp

 theorem pairedBackground_difference_support {p : ℕ} (S T : State (2*p) p)
    (h : (pairedBackground p-1) S T ≠ 0) : S.weight+1≤T.weight := by
  by_cases he:S=T
  · subst T; simp at h
  · have hf : pairedBackground p S T ≠ 0 := by simpa [Matrix.one_apply,he] using h
    have h1 := pairedBackground_weight_le S T hf
    have h2 : S.weight≠T.weight := fun hw => he (pairedBackground_eq_states S T hf hw)
    omega

/-- The paired background has exactly the polynomial nilpotence exponent used in Lemma3.3. -/
theorem pairedBackground_nilpotent (p : ℕ) : (pairedBackground p-1)^(p^2+1)=0 := by
  apply potential_nilpotent _ State.weight (minWeight p) (p^2)
    (fun S T => pairedBackground_difference_support S T) state_weight_lower
  intro S
  have hs := state_weight_upper S
  simpa only [show 2*p-p=p by omega,pow_two] using hs

/-- The previously constructed inverse is also the finite polynomial geometric series. -/
theorem pairedInverse_series (p : ℕ) :
    pairedInverse p = inverseSeries (pairedBackground p-1) (p^2) := by
  have hs := inverseSeries_mul (pairedBackground p-1) (p^2) (pairedBackground_nilpotent p)
  have hs' : inverseSeries (pairedBackground p-1) (p^2) * pairedBackground p=1 := by
    simpa using hs
  calc
    pairedInverse p = 1*pairedInverse p := (one_mul _).symm
    _ = (inverseSeries (pairedBackground p-1) (p^2)*pairedBackground p)*pairedInverse p := by rw [hs']
    _ = inverseSeries (pairedBackground p-1) (p^2) := by rw [Matrix.mul_assoc,mul_pairedInverse,mul_one]

end HiddenCircuits
