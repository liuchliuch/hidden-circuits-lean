import HiddenCircuits.GraphReduction.UnitIntervalConstructionBounds
import Mathlib.Data.Nat.Size

/-! Common-denominator natural-number implementation of midpoint coordinates.
At stage n the denominator is 2^n. Extending the model doubles every old
numerator, and computes the new one with only maxima, minima, and addition. -/
namespace HiddenCircuits.GraphReduction.UnitIntervalOrder.Dyadic

def lower {n : ℕ} (G : SimpleGraph (Fin (n+1))) [DecidableRel G.Adj]
    (u : Fin n → ℕ) (D : ℕ) : Finset ℕ :=
  insert 0 (Finset.univ.image u ∪
    (Finset.univ.filter (fun i : Fin n => ¬G.Adj i.castSucc (Fin.last n))).image (fun i => u i+D))
def upper {n : ℕ} (G : SimpleGraph (Fin (n+1))) [DecidableRel G.Adj]
    (u : Fin n → ℕ) (D : ℕ) : Finset ℕ :=
  (Finset.univ.filter (fun i : Fin n => G.Adj i.castSucc (Fin.last n))).image (fun i => u i+D)
lemma lower_nonempty {n : ℕ} (G : SimpleGraph (Fin (n+1))) [DecidableRel G.Adj]
    (u : Fin n → ℕ) (D : ℕ) : (lower G u D).Nonempty := ⟨0,by simp [lower]⟩

def next {n : ℕ} (G : SimpleGraph (Fin (n+1))) [DecidableRel G.Adj]
    (u : Fin n → ℕ) (D : ℕ) : ℕ :=
  let a := (lower G u D).max' (lower_nonempty G u D)
  if h : (upper G u D).Nonempty then a+(upper G u D).min' h else 2*(a+D)

def numerators : ∀ n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], Fin n → ℕ
  | 0,_,_ => Fin.elim0
  | n+1,G,_ =>
    let u := numerators n (G.comap Fin.castSucc)
    Fin.snoc (fun i => 2*u i) (next G u (2^n))

lemma lower_scale {n : ℕ} (G : SimpleGraph (Fin (n+1))) [DecidableRel G.Adj]
    (u : Fin n → ℕ) {D : ℕ} (hD : 0 < D) :
    lowerBounds G (fun i => (u i : ℚ)/D) = (lower G u D).image (fun a : ℕ => (a : ℚ)/D) := by
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  simp only [lowerBounds,lower,Finset.image_insert,Finset.image_union,Finset.image_image,
    Function.comp_def,Nat.cast_zero,zero_div,Nat.cast_add,add_div,div_self hDq]

lemma upper_scale {n : ℕ} (G : SimpleGraph (Fin (n+1))) [DecidableRel G.Adj]
    (u : Fin n → ℕ) {D : ℕ} (hD : 0 < D) :
    upperBounds G (fun i => (u i : ℚ)/D) = (upper G u D).image (fun a : ℕ => (a : ℚ)/D) := by
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  simp only [upperBounds,upper,Finset.image_image,Function.comp_def,Nat.cast_add,add_div,div_self hDq]

lemma next_scale {n : ℕ} (G : SimpleGraph (Fin (n+1))) [DecidableRel G.Adj]
    (u : Fin n → ℕ) {D : ℕ} (hD : 0 < D) :
    (next G u D : ℚ)/(2*D) = separator
      (lowerBounds G (fun i => (u i : ℚ)/D)) (upperBounds G (fun i => (u i : ℚ)/D))
      (lowerBounds_nonempty _ _) := by
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  have hm : Monotone (fun a : ℕ => (a : ℚ)/D) := by
    intro a b hab
    exact div_le_div_of_nonneg_right (by exact_mod_cast hab) (by positivity)
  simp only [lower_scale G u hD,upper_scale G u hD]
  unfold next separator
  simp only [Finset.image_nonempty]
  split_ifs with hB
  · rw [Finset.max'_image hm,Finset.min'_image hm]
    push_cast
    field_simp
    <;> ring
  · rw [Finset.max'_image hm]
    push_cast
    field_simp
    <;> ring

/-- The integer-only implementation computes exactly the proved rational
midpoint model. It requires no order certificate at runtime. -/
theorem numerators_refine : ∀ n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : Umbrella G) (v : Fin n),
    (numerators n G v : ℚ)/(2^n : ℕ) = (buildModel n G h).left v := by
  intro n
  induction n with
  | zero => intro G _ h v; exact Fin.elim0 v
  | succ n ih =>
    intro G _ h v
    let H := G.comap Fin.castSucc
    have hH : Umbrella H := fun i j k hij hjk he => h i.castSucc j.castSucc k.castSucc hij hjk he
    have he : (fun i => (numerators n H i : ℚ)/(2^n : ℕ)) = (buildModel n H hH).left := by
      funext i; exact ih H hH i
    refine Fin.lastCases ?_ (fun i => ?_) v
    · rw [numerators,Fin.snoc_last,buildModel_last]
      dsimp only
      rw [←he]
      convert next_scale G (numerators n H) (by positivity : 0 < 2^n) using 1 <;> push_cast <;> ring
    · rw [numerators,Fin.snoc_castSucc,buildModel_castSucc]
      rw [←ih H hH i]
      push_cast
      rw [pow_succ]
      field_simp
      <;> ring

/-- The uncompressed integer registers have at most a linear number of bits:
all nonnegative numerators are bounded by 2n·2^n. -/
theorem numerators_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : Umbrella G) (v : Fin n) : numerators n G v ≤ 2*n*2^n := by
  have hb := buildModel_left_bound n G h v
  rw [←numerators_refine n G h v] at hb
  have hp : (0 : ℚ) < (2^n : ℕ) := by positivity
  have hh := (div_le_iff₀ hp).mp hb
  exact_mod_cast hh

/-- Explicit linear binary-magnitude bound for every constructed numerator. -/
theorem numerators_size {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : Umbrella G) (v : Fin n) : (numerators n G v).size ≤ 2*n+1 := by
  have hn : n < 2^n := Nat.lt_two_pow_self
  have hn2 : 2*n < 2^(n+1) := by rw [pow_succ]; omega
  have hn3 := Nat.mul_lt_mul_of_pos_right hn2 (show 0 < 2^n by positivity)
  rw [←pow_add] at hn3
  have he : n+1+n = 2*n+1 := by omega
  rw [he] at hn3
  exact Nat.size_le.mpr ((numerators_bound G h v).trans_lt hn3)

@[simp] theorem denominator_size (n : ℕ) : (2^n).size = n+1 := Nat.size_pow

end HiddenCircuits.GraphReduction.UnitIntervalOrder.Dyadic
