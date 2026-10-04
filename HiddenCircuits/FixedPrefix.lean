import HiddenCircuits.FlowSupport
import HiddenCircuits.PermanentBlocks

/-! Fixed occupied positions for the actual normalized transfer matrices. -/
namespace HiddenCircuits
open scoped BigOperators

namespace Straightening

/-- A product of upper row forms, allowing repeated row indices. -/
def rowProduct {n q : ℕ} (f : Fin q → ℕ) (T : State n q) : ℚ :=
  Matrix.permanent (fun a b => if f a ≤ (T.track b).val then (1 : ℚ) else 0)

/-- Coordinates of a possibly repeated product in the distinct-row basis. -/
def coordinates {n q : ℕ} (f : Fin q → ℕ) (T : State n q) : ℚ :=
  ∑ K : State n q, rowProduct f K * upperInverse n q K T

/-- The permanent may equivalently be summed with the chosen permutation on columns. -/
theorem rowProduct_eq {n q : ℕ} (f : Fin q → ℕ) (T : State n q) :
    rowProduct f T = ∑ σ : Equiv.Perm (Fin q),
      ∏ a, if f a ≤ (T.track (σ a)).val then (1 : ℚ) else 0 := by
  unfold rowProduct
  rw [← Matrix.permanent_transpose]
  rfl

/-- A row beyond the final track is the zero form. -/
theorem rowProduct_zero {n q : ℕ} (f : Fin q → ℕ) (T : State n q)
    (a : Fin q) (ha : n ≤ f a) : rowProduct f T = 0 := by
  rw [rowProduct_eq]
  apply Finset.sum_eq_zero
  intro σ _
  apply Finset.prod_eq_zero (Finset.mem_univ a)
  have hx := (T.track (σ a)).isLt
  simp [show ¬ f a ≤ (T.track (σ a)).val by omega]

theorem coordinates_zero {n q : ℕ} (f : Fin q → ℕ) (T : State n q)
    (a : Fin q) (ha : n ≤ f a) : coordinates f T = 0 := by
  unfold coordinates
  simp [rowProduct_zero f _ a ha]

/-- Split two factors off a finite product. -/
theorem prod_two {α R : Type*} [Fintype α] [DecidableEq α] [CommMonoid R]
    (f : α → R) (a b : α) (hab : a ≠ b) :
    ∏ x, f x = f a * f b * ∏ x ∈ (Finset.univ.erase a).erase b, f x := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a),
    ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hab.symm,Finset.mem_univ b⟩)]
  simp [mul_assoc]

/-- The elementary square-free relation, expressed directly in actual permanents.
Both mixed products are retained, so no symmetry or quotient-algebra axiom is needed. -/
theorem rowProduct_straighten {n q : ℕ} (f : Fin q → ℕ) (T : State n q)
    (a b : Fin q) (hab : a ≠ b) (he : f a = f b) :
    rowProduct f T =
      rowProduct (Function.update f a (f a + 1)) T +
      rowProduct (Function.update f b (f a + 1)) T -
      rowProduct (Function.update (Function.update f a (f a + 1)) b (f a + 1)) T := by
  classical
  simp only [rowProduct_eq, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  have hx : (T.track (σ a)).val ≠ (T.track (σ b)).val := by
    intro h
    exact hab (σ.injective (T.track.injective (Fin.ext h)))
  rw [prod_two _ a b hab, prod_two _ a b hab, prod_two _ a b hab,
    prod_two _ a b hab]
  have hprod : ∀ g : Fin q → ℕ, (∀ x, x ≠ a → x ≠ b → g x = f x) →
      (∏ x ∈ (Finset.univ.erase a).erase b,
        if g x ≤ (T.track (σ x)).val then (1 : ℚ) else 0) =
      ∏ x ∈ (Finset.univ.erase a).erase b,
        if f x ≤ (T.track (σ x)).val then (1 : ℚ) else 0 := by
    intro g hg
    apply Finset.prod_congr rfl
    intro x hx
    rw [hg x (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
      (Finset.mem_erase.mp hx).1]
  rw [hprod (Function.update f a (f a + 1)) (by intros; simp_all),
    hprod (Function.update f b (f a + 1)) (by intros; simp_all),
    hprod (Function.update (Function.update f a (f a + 1)) b (f a + 1))
      (by intros; simp_all)]
  simp only [Function.update_self, Function.update_of_ne hab,
    Function.update_of_ne hab.symm, ← he]
  have hscalar :
      (if f a ≤ (T.track (σ a)).val then (1 : ℚ) else 0) *
        (if f a ≤ (T.track (σ b)).val then (1 : ℚ) else 0) =
      (if f a + 1 ≤ (T.track (σ a)).val then (1 : ℚ) else 0) *
        (if f a ≤ (T.track (σ b)).val then (1 : ℚ) else 0) +
      (if f a ≤ (T.track (σ a)).val then (1 : ℚ) else 0) *
        (if f a + 1 ≤ (T.track (σ b)).val then (1 : ℚ) else 0) -
      (if f a + 1 ≤ (T.track (σ a)).val then (1 : ℚ) else 0) *
        (if f a + 1 ≤ (T.track (σ b)).val then (1 : ℚ) else 0) := by
    split_ifs <;> first | omega | norm_num
  rw [hscalar]
  ring

 theorem coordinates_straighten {n q : ℕ} (f : Fin q → ℕ) (T : State n q)
    (a b : Fin q) (hab : a ≠ b) (he : f a = f b) :
    coordinates f T =
      coordinates (Function.update f a (f a + 1)) T +
      coordinates (Function.update f b (f a + 1)) T -
      coordinates (Function.update (Function.update f a (f a + 1)) b (f a + 1)) T := by
  unfold coordinates
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro K _
  rw [rowProduct_straighten f K a b hab he]
  ring

/-- Distinct row indices are precisely a genuine subset state, up to row ordering. -/
theorem coordinates_injective {n q : ℕ} (f : Fin q → ℕ)
    (hf : ∀ a, f a < n) (hinj : Function.Injective f) :
    ∃ S : State n q, (∀ x : Fin n, x ∈ S.val ↔ ∃ a, f a = x.val) ∧
      ∀ T, coordinates f T = (1 : Matrix (State n q) (State n q) ℚ) S T := by
  classical
  let g : Fin q → Fin n := fun a => ⟨f a,hf a⟩
  have hg : Function.Injective g := fun a b h => hinj (congrArg Fin.val h)
  let S : State n q := ⟨Finset.univ.image g, by
    rw [Finset.card_image_of_injective _ hg]
    simp⟩
  have hmem (a : Fin q) : g a ∈ S.val := Finset.mem_image.mpr ⟨a,Finset.mem_univ a,rfl⟩
  let e₀ : Fin q ≃ S.val := Equiv.ofBijective (fun a => ⟨g a,hmem a⟩) (by
    constructor
    · intro a b h; exact hg (congrArg Subtype.val h)
    · rintro ⟨x,hx⟩
      obtain ⟨a,_,ha⟩ := Finset.mem_image.mp hx
      exact ⟨a,Subtype.ext ha⟩)
  let e : Fin q ≃ Fin q := e₀.trans (S.val.orderIsoOfFin S.property).toEquiv.symm
  have he (a : Fin q) : S.track (e a) = g a := by
    change ((S.val.orderIsoOfFin S.property)
      ((S.val.orderIsoOfFin S.property).symm (e₀ a))).val = _
    simp [e₀]
  refine ⟨S,?_,?_⟩
  · intro x
    change x ∈ Finset.univ.image g ↔ _
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨a,ha⟩; exact ⟨a,congrArg Fin.val ha⟩
    · rintro ⟨a,ha⟩; exact ⟨a,Fin.ext ha⟩
  · intro T
    have hrow (K : State n q) : rowProduct f K = compound (upper n) S K := by
      have hp := Matrix.permanent_permute_cols e
        ((upper n).submatrix S.track K.track)
      convert hp using 1
      unfold rowProduct
      congr 1
      ext a b
      simp only [Matrix.submatrix_apply,upper,he]
      rfl
    simp only [coordinates,hrow]
    exact congrFun (congrFun (mul_upperInverse n q) S) T

/-- No index below the chosen cut occurs twice in the row product. -/
def LowDistinct {q : ℕ} (f : Fin q → ℕ) (i : ℕ) : Prop :=
  ∀ a b, f a < i → f a = f b → a = b

def remaining {q : ℕ} (n : ℕ) (f : Fin q → ℕ) : ℕ := ∑ a : Fin q, (n - f a)

theorem remaining_update_lt {q : ℕ} (n : ℕ) (f : Fin q → ℕ) (a : Fin q)
    (ha : f a < n) : remaining n (Function.update f a (f a+1)) < remaining n f := by
  unfold remaining
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
  simp only [Function.update_self]
  have hsum : (∑ x ∈ Finset.univ.erase a, (n - Function.update f a (f a+1) x)) =
      ∑ x ∈ Finset.univ.erase a, (n - f x) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Function.update_of_ne (Finset.mem_erase.mp hx).1]
  rw [hsum]
  omega

 theorem lowDistinct_update {q : ℕ} (f : Fin q → ℕ) (i : ℕ)
    (h : LowDistinct f i) (a : Fin q) (_ha : i ≤ f a) (v : ℕ) (hv : i ≤ v) :
    LowDistinct (Function.update f a v) i := by
  intro b c hb he
  by_cases hba : b=a
  · subst b; simp only [Function.update_self] at hb; omega
  by_cases hca : c=a
  · subst c
    rw [Function.update_self,Function.update_of_ne hba] at he
    rw [Function.update_of_ne hba] at hb
    omega
  rw [Function.update_of_ne hba] at hb
  rw [Function.update_of_ne hba,Function.update_of_ne hca] at he
  exact h b c hb he

 theorem lowRange_update {q : ℕ} (f : Fin q → ℕ) (i : ℕ)
    (a : Fin q) (ha : i ≤ f a) (v : ℕ) (hv : i ≤ v) (x : ℕ) (hx : x < i) :
    (∃ b, Function.update f a v b=x) ↔ ∃ b, f b=x := by
  constructor
  · rintro ⟨b,hb⟩
    by_cases hba:b=a
    · subst b; simp only [Function.update_self] at hb; omega
    · exact ⟨b,by simpa [hba] using hb⟩
  · rintro ⟨b,hb⟩
    have hba:b≠a := by rintro rfl; omega
    exact ⟨b,by simpa [hba] using hb⟩

/-- Straightening cannot change a row index below a cut where the indices were
already distinct. This is a support theorem for the actual finite inverse. -/
theorem coordinates_fixed_prefix {n q : ℕ} (f : Fin q → ℕ) (T : State n q)
    (i : ℕ) (hd : LowDistinct f i) (hn : coordinates f T ≠ 0) :
    ∀ x : Fin n, x.val < i → (x ∈ T.val ↔ ∃ a, f a = x.val) := by
  classical
  have H : ∀ k, ∀ g : Fin q → ℕ, remaining n g = k →
      LowDistinct g i → coordinates g T ≠ 0 →
      ∀ x : Fin n, x.val < i → (x ∈ T.val ↔ ∃ a, g a = x.val) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro g hk hg hn
      by_cases hbound : ∀ a, g a < n
      · by_cases hinj : Function.Injective g
        · obtain ⟨S, hmem, hc⟩ := coordinates_injective g hbound hinj
          have he : S = T := by
            by_contra hne
            exact hn (by simpa [Matrix.one_apply,hne] using hc T)
          subst S
          exact fun x _ => hmem x
        · have hp : ∃ a b, g a = g b ∧ a ≠ b := by
            simpa [Function.Injective] using hinj
          obtain ⟨a,b,he,hab⟩ := hp
          have hia : i ≤ g a := by
            by_contra hlt
            exact hab (hg a b (by omega) he)
          have hib : i ≤ g b := by omega
          let g₁ := Function.update g a (g a + 1)
          let g₂ := Function.update g b (g a + 1)
          let g₃ := Function.update g₁ b (g a + 1)
          have h₁ : remaining n g₁ < k := by
            rw [← hk]
            exact remaining_update_lt n g a (hbound a)
          have h₂ : remaining n g₂ < k := by
            rw [← hk]
            simpa only [g₂,he] using remaining_update_lt n g b (hbound b)
          have h₃ : remaining n g₃ < k := by
            apply lt_trans _ h₁
            have hb : g₁ b = g b := by simp [g₁,hab.symm]
            have hlt := remaining_update_lt n g₁ b (by rw [hb]; exact hbound b)
            simpa only [g₃,hb,← he] using hlt
          have hd₁ : LowDistinct g₁ i := lowDistinct_update g i hg a hia _ (by omega)
          have hd₂ : LowDistinct g₂ i := lowDistinct_update g i hg b hib _ (by omega)
          have hd₃ : LowDistinct g₃ i := by
            apply lowDistinct_update g₁ i hd₁ b _ _ (by omega)
            simpa [g₁,hab.symm] using hib
          have hr₁ (x : Fin n) (hx : x.val < i) :
              (∃ b, g₁ b = x.val) ↔ ∃ b, g b = x.val :=
            lowRange_update g i a hia _ (by omega) x.val hx
          have hr₂ (x : Fin n) (hx : x.val < i) :
              (∃ b, g₂ b = x.val) ↔ ∃ b, g b = x.val :=
            lowRange_update g i b hib _ (by omega) x.val hx
          have hr₃ (x : Fin n) (hx : x.val < i) :
              (∃ b, g₃ b = x.val) ↔ ∃ b, g b = x.val := by
            apply Iff.trans (lowRange_update g₁ i b _ _ (by omega) x.val hx) (hr₁ x hx)
            simpa [g₁,hab.symm] using hib
          by_cases hn₁ : coordinates g₁ T ≠ 0
          · exact fun x hx => (ih _ h₁ g₁ rfl hd₁ hn₁ x hx).trans (hr₁ x hx)
          by_cases hn₂ : coordinates g₂ T ≠ 0
          · exact fun x hx => (ih _ h₂ g₂ rfl hd₂ hn₂ x hx).trans (hr₂ x hx)
          have hn₃ : coordinates g₃ T ≠ 0 := by
            intro hz
            apply hn
            rw [coordinates_straighten g T a b hab he]
            change coordinates g₁ T + coordinates g₂ T - coordinates g₃ T = 0
            simp only [not_not.mp hn₁, not_not.mp hn₂, hz]
            norm_num
          exact fun x hx => (ih _ h₃ g₃ rfl hd₃ hn₃ x hx).trans (hr₃ x hx)
      · push_neg at hbound
        obtain ⟨a,ha⟩ := hbound
        exact False.elim (hn (coordinates_zero g T a ha))
  exact H _ f rfl hd hn

/-- A convenient form with the unchanged low indices identified with an input state. -/
theorem coordinates_preserve_low {n q : ℕ} (f : Fin q → ℕ) (S T : State n q)
    (i : ℕ) (hlow : ∀ a x, x < i → (f a = x ↔ (S.track a).val = x))
    (hn : coordinates f T ≠ 0) :
    ∀ x : Fin n, x.val < i → (x ∈ S.val ↔ x ∈ T.val) := by
  have hd : LowDistinct f i := by
    intro a b ha he
    apply S.track.injective
    apply Fin.ext
    exact ((hlow a (f a) ha).mp rfl).trans ((hlow b (f a) ha).mp he.symm).symm
  intro x hx
  have hh := coordinates_fixed_prefix f T i hd hn x hx
  rw [hh]
  have hs : x ∈ S.val ↔ ∃ a, (S.track a).val = x.val := by
    rw [← S.image_track]
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    exact exists_congr (fun a => Fin.ext_iff)
  rw [hs]
  exact exists_congr (fun a => (hlow a x.val hx).symm)

end Straightening

/-- The changed row index for deletion of the diagonal edge. -/
def dropRows {n q : ℕ} (S : State n q) (i : Fin (n-1)) : Fin q → ℕ :=
  fun a => if (S.track a).val = i.val then i.val + 1 else (S.track a).val

/-- The changed row index for addition of the subdiagonal edge. -/
def riseRows {n q : ℕ} (S : State n q) (i : Fin (n-1)) : Fin q → ℕ :=
  fun a => if (S.track a).val = i.val + 1 then i.val else (S.track a).val

/-- Actual deletion is exactly the row-product replacement, before normalization. -/
theorem compound_deleted_rowProduct {n q : ℕ} (S T : State n q) (i : Fin (n-1)) :
    compound (deletedCut i) S T = Straightening.rowProduct (dropRows S i) T := by
  unfold compound Straightening.rowProduct
  congr 1
  ext a b
  simp only [Matrix.submatrix_apply,deletedCut,upper,dropRows]
  split_ifs <;> simp_all only [Fin.le_iff_val_le_val, true_and, false_and,
    not_true_eq_false, not_false_eq_true] <;> omega

/-- Actual addition is exactly the row-product replacement, before normalization. -/
theorem compound_added_rowProduct {n q : ℕ} (S T : State n q) (i : Fin (n-1)) :
    compound (addedCut i) S T = Straightening.rowProduct (riseRows S i) T := by
  unfold compound Straightening.rowProduct
  congr 1
  ext a b
  simp only [Matrix.submatrix_apply,addedCut,upper,riseRows]
  split_ifs <;> simp_all only [Fin.le_iff_val_le_val, true_and, false_and,
    not_true_eq_false, not_false_eq_true] <;> omega

theorem drop_eq_coordinates {n q : ℕ} (S T : State n q) (i : Fin (n-1)) :
    drop n q i S T = Straightening.coordinates (dropRows S i) T := by
  simp only [drop,Matrix.mul_apply,Straightening.coordinates,compound_deleted_rowProduct]

theorem rise_eq_coordinates {n q : ℕ} (S T : State n q) (i : Fin (n-1)) :
    rise n q i S T = Straightening.coordinates (riseRows S i) T := by
  simp only [rise,Matrix.mul_apply,Straightening.coordinates,compound_added_rowProduct]

/-- The deletion transfer fixes every occupied position strictly before its index. -/
theorem drop_fixed_prefix {n q : ℕ} (i : Fin (n-1)) (S T : State n q)
    (hn : drop n q i S T ≠ 0) :
    ∀ x : Fin n, x.val < i.val → (x ∈ S.val ↔ x ∈ T.val) := by
  rw [drop_eq_coordinates] at hn
  apply Straightening.coordinates_preserve_low (dropRows S i) S T i.val _ hn
  intro a x hx
  unfold dropRows
  split_ifs <;> omega

/-- The rise transfer fixes every occupied position strictly before its index. -/
theorem rise_fixed_prefix {n q : ℕ} (i : Fin (n-1)) (S T : State n q)
    (hn : rise n q i S T ≠ 0) :
    ∀ x : Fin n, x.val < i.val → (x ∈ S.val ↔ x ∈ T.val) := by
  rw [rise_eq_coordinates] at hn
  apply Straightening.coordinates_preserve_low (riseRows S i) S T i.val _ hn
  intro a x hx
  unfold riseRows
  split_ifs <;> omega

theorem dualDrop_fixed_prefix {n q : ℕ} (i : Fin (n-1)) (S T : State n q)
    (hn : dualDrop n q i S T ≠ 0) :
    ∀ x : Fin n, x.val < i.val → (x ∈ S.val ↔ x ∈ T.val) := by
  intro x hx
  have hh := drop_fixed_prefix i T.complement S.complement hn x hx
  simpa using hh.not.symm

theorem dualRise_fixed_prefix {n q : ℕ} (i : Fin (n-1)) (S T : State n q)
    (hn : dualRise n q i S T ≠ 0) :
    ∀ x : Fin n, x.val < i.val → (x ∈ S.val ↔ x ∈ T.val) := by
  intro x hx
  have hh := rise_fixed_prefix i T.complement S.complement hn x hx
  simpa using hh.not.symm

/-- Fixed-position half of Lemma 4.1, for all four actual normalized transfers. -/
theorem letter_fixed_prefix {n q : ℕ} (l : Letter n) (S T : State n q)
    (hn : l.matrix q S T ≠ 0) :
    ∀ x : Fin n, x.val < l.index.val → (x ∈ S.val ↔ x ∈ T.val) := by
  cases l with
  | mk kind i =>
    cases kind with
    | R => exact rise_fixed_prefix i S T hn
    | D => exact drop_fixed_prefix i S T hn
    | B => exact dualRise_fixed_prefix i S T hn
    | E => exact dualDrop_fixed_prefix i S T hn

/-- The set form of the fixed-prefix conclusion in Lemma 4.1. -/
theorem letter_fixed_prefix_set {n q : ℕ} (l : Letter n) (S T : State n q)
    (hn : l.matrix q S T ≠ 0) :
    S.val.filter (fun x => x.val < l.index.val) =
      T.val.filter (fun x => x.val < l.index.val) := by
  ext x
  simp only [Finset.mem_filter]
  by_cases hx : x.val < l.index.val
  · rw [letter_fixed_prefix l S T hn x hx]
  · simp [hx]

/-- A word fixes all positions preceding every index used by that word. -/
theorem word_fixed_prefix {n q : ℕ} (w : List (Letter n)) (c : ℕ)
    (hc : ∀ l ∈ w, c ≤ l.index.val) :
    ∀ S T : State n q, wordMatrix q w S T ≠ 0 →
      ∀ x : Fin n, x.val < c → (x ∈ S.val ↔ x ∈ T.val) := by
  induction w with
  | nil =>
    intro S T hn x _
    have he : S = T := by
      by_contra hne
      exact hn (by simp [hne])
    rw [he]
  | cons l w ih =>
    intro S T hn x hx
    rw [wordMatrix_cons,Matrix.mul_apply] at hn
    obtain ⟨K,_,hK⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
    have hSK := letter_fixed_prefix l S K
      (fun hz => hK (by rw [hz,zero_mul])) x
      (lt_of_lt_of_le hx (hc l (by simp)))
    exact hSK.trans (ih (fun a ha => hc a (by simp [ha])) K T
      (fun hz => hK (by rw [hz,mul_zero])) x hx)

/-- Lemma 4.1: fixed low positions and the precise exceptional-cut flow bound,
proved for the globally defined permanental-compound transfers. -/
theorem letter_flow {n q : ℕ} (l : Letter n) (S T : State n q)
    (hn : l.matrix q S T ≠ 0) :
    (S.val.filter (fun x => x.val < l.index.val) =
      T.val.filter (fun x => x.val < l.index.val)) ∧
    ∀ c, T.prefixCount c ≤ S.prefixCount c +
      (match l.kind with
       | .R | .B => if c = l.index.val + 1 then 1 else 0
       | .D | .E => 0) := by
  refine ⟨letter_fixed_prefix_set l S T hn, ?_⟩
  cases l with
  | mk kind i =>
    cases kind with
    | R => exact rise_prefix_bound n q i S T hn
    | D => simpa using drop_prefix_flow n q i S T hn
    | B => exact dualRise_prefix_bound n q i S T hn
    | E => simpa using dualDrop_prefix_flow n q i S T hn

end HiddenCircuits
