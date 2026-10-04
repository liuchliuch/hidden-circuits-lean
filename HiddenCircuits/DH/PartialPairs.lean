import HiddenCircuits.DH.CrossPairs

/-! Concrete finite partial bijections and their exact endpoint-choice fibers. -/
namespace HiddenCircuits.DH

/-- Two partial partner maps describe the same collection of disjoint cross pairs. -/
@[ext] structure PartialPairs (V W : Type*) where
  left : V → Option W
  right : W → Option V
  symm : ∀ v w, left v = some w ↔ right w = some v

namespace PartialPairs
variable {V W : Type*}

lemma ext_left {p q : PartialPairs V W} (h : p.left = q.left) : p = q := by
  apply PartialPairs.ext h
  funext w
  apply Option.ext
  intro v
  rw [← p.symm, ← q.symm, h]

lemma ext_right {p q : PartialPairs V W} (h : p.right = q.right) : p = q := by
  apply PartialPairs.ext _ h
  funext v
  apply Option.ext
  intro w
  rw [p.symm, q.symm, h]

noncomputable instance [Fintype V] [Fintype W] : Fintype (PartialPairs V W) := by
  classical
  exact Fintype.ofInjective (fun p => p.left) (fun _ _ => ext_left)

noncomputable instance [Fintype V] [Fintype W] : DecidableEq (PartialPairs V W) :=
  Classical.decEq _

section Finite
variable [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- The vertices at the left endpoints of the partial pairs. -/
def leftDomain (p : PartialPairs V W) : Finset V :=
  Finset.univ.filter fun v => (p.left v).isSome

/-- The vertices at the right endpoints of the partial pairs. -/
def rightDomain (p : PartialPairs V W) : Finset W :=
  Finset.univ.filter fun w => (p.right w).isSome

@[simp] lemma mem_leftDomain (p : PartialPairs V W) (v : V) :
    v ∈ p.leftDomain ↔ ∃ w, p.left v = some w := by
  simp [leftDomain, Option.isSome_iff_exists]

@[simp] lemma mem_rightDomain (p : PartialPairs V W) (w : W) :
    w ∈ p.rightDomain ↔ ∃ v, p.right w = some v := by
  simp [rightDomain, Option.isSome_iff_exists]

/-- The number of cross pairs is the number of covered left vertices. -/
def rank (p : PartialPairs V W) : ℕ := p.leftDomain.card

noncomputable def leftValue (p : PartialPairs V W) (v : p.leftDomain) : W :=
  ((p.mem_leftDomain v.val).mp v.property).choose

lemma left_leftValue (p : PartialPairs V W) (v : p.leftDomain) :
    p.left v.val = some (p.leftValue v) :=
  ((p.mem_leftDomain v.val).mp v.property).choose_spec

noncomputable def rightValue (p : PartialPairs V W) (w : p.rightDomain) : V :=
  ((p.mem_rightDomain w.val).mp w.property).choose

lemma right_rightValue (p : PartialPairs V W) (w : p.rightDomain) :
    p.right w.val = some (p.rightValue w) :=
  ((p.mem_rightDomain w.val).mp w.property).choose_spec

/-- The partner maps restrict to a genuine equivalence of their covered domains. -/
noncomputable def domainEquiv (p : PartialPairs V W) : p.leftDomain ≃ p.rightDomain where
  toFun v := ⟨p.leftValue v, (p.mem_rightDomain _).mpr
    ⟨v.val, (p.symm _ _).mp (p.left_leftValue v)⟩⟩
  invFun w := ⟨p.rightValue w, (p.mem_leftDomain _).mpr
    ⟨w.val, (p.symm _ _).mpr (p.right_rightValue w)⟩⟩
  left_inv v := by
    apply Subtype.ext
    apply Option.some.inj
    exact (p.right_rightValue _).symm.trans ((p.symm _ _).mp (p.left_leftValue v))
  right_inv w := by
    apply Subtype.ext
    apply Option.some.inj
    exact (p.left_leftValue _).symm.trans ((p.symm _ _).mpr (p.right_rightValue w))

/-- A partial bijection covers equally many vertices on both sides. -/
theorem domain_card_eq (p : PartialPairs V W) :
    p.leftDomain.card = p.rightDomain.card := by
  simpa only [Fintype.card_coe] using Fintype.card_congr p.domainEquiv

/-- A bijection between selected endpoints defines partial partner maps. -/
def ofEquiv (s : Finset V) (t : Finset W) (e : s ≃ t) : PartialPairs V W where
  left v := if h : v ∈ s then some (e ⟨v,h⟩).val else none
  right w := if h : w ∈ t then some (e.symm ⟨w,h⟩).val else none
  symm v w := by
    constructor
    · intro h
      split_ifs at h with hv
      · have he : (e ⟨v,hv⟩).val = w := Option.some.inj h
        have hw : w ∈ t := he ▸ (e ⟨v,hv⟩).property
        rw [dif_pos hw]
        congr 1
        have hes : e ⟨v,hv⟩ = ⟨w,hw⟩ := Subtype.ext he
        simpa using congrArg Subtype.val (congrArg e.symm hes).symm
    · intro h
      split_ifs at h with hw
      · have he : (e.symm ⟨w,hw⟩).val = v := Option.some.inj h
        have hv : v ∈ s := he ▸ (e.symm ⟨w,hw⟩).property
        rw [dif_pos hv]
        congr 1
        have hes : e.symm ⟨w,hw⟩ = ⟨v,hv⟩ := Subtype.ext he
        simpa using congrArg Subtype.val (congrArg e hes).symm

@[simp] lemma ofEquiv_leftDomain (s : Finset V) (t : Finset W) (e : s ≃ t) :
    (ofEquiv s t e).leftDomain = s := by
  ext v
  simp only [mem_leftDomain, ofEquiv]
  by_cases h : v ∈ s <;> simp [h]

@[simp] lemma ofEquiv_rightDomain (s : Finset V) (t : Finset W) (e : s ≃ t) :
    (ofEquiv s t e).rightDomain = t := by
  ext w
  simp only [mem_rightDomain, ofEquiv]
  by_cases h : w ∈ t <;> simp [h]

@[simp] lemma ofEquiv_rank (s : Finset V) (t : Finset W) (e : s ≃ t) :
    (ofEquiv s t e).rank = s.card := by simp [rank]

@[simp] lemma ofEquiv_domainEquiv (p : PartialPairs V W) :
    ofEquiv p.leftDomain p.rightDomain p.domainEquiv = p := by
  apply ext_left
  funext v
  change (if h : v ∈ p.leftDomain then some (p.leftValue ⟨v,h⟩) else none) = p.left v
  split_ifs with h
  · exact (p.left_leftValue ⟨v,h⟩).symm
  · cases hv : p.left v with
    | none => rfl
    | some w => exact (h ((p.mem_leftDomain v).mpr ⟨w,hv⟩)).elim

/-- Forget the selected-endpoint packaging, retaining the concrete partner maps. -/
def fromCrossPairs {r : ℕ} (c : CrossPairs V W r) : PartialPairs V W :=
  ofEquiv c.1.val c.2.1.val c.2.2

@[simp] lemma fromCrossPairs_rank {r : ℕ} (c : CrossPairs V W r) :
    (fromCrossPairs c).rank = r := by
  simp only [fromCrossPairs, ofEquiv_rank]
  exact selected_size V c.1

lemma fromCrossPairs_injective (r : ℕ) :
    Function.Injective (fromCrossPairs (V := V) (W := W) (r := r)) := by
  rintro ⟨s,t,e⟩ ⟨s',t',e'⟩ h
  have hs : s = s' := by
    apply Subtype.ext
    have hd := congrArg leftDomain h
    simpa only [fromCrossPairs, ofEquiv_leftDomain] using hd
  subst s'
  have ht : t = t' := by
    apply Subtype.ext
    have hd := congrArg rightDomain h
    simpa only [fromCrossPairs, ofEquiv_rightDomain] using hd
  subst t'
  have he : e = e' := by
    apply Equiv.ext
    intro v
    apply Subtype.ext
    apply Option.some.inj
    have hp := congrArg (fun p : PartialPairs V W => p.left v.val) h
    simpa only [fromCrossPairs, ofEquiv, dif_pos v.property] using hp
  subst e'
  rfl

/-- Read off the two covered endpoint sets and the actual partner bijection. -/
noncomputable def toCrossPairs {r : ℕ} (p : PartialPairs V W) (hr : p.rank = r) :
    CrossPairs V W r :=
  ⟨⟨p.leftDomain, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hr⟩⟩,
   ⟨p.rightDomain, Finset.mem_powersetCard.mpr
     ⟨Finset.subset_univ _, p.domain_card_eq.symm.trans hr⟩⟩, p.domainEquiv⟩

@[simp] lemma from_toCrossPairs {r : ℕ} (p : PartialPairs V W) (hr : p.rank = r) :
    fromCrossPairs (p.toCrossPairs hr) = p :=
  ofEquiv_domainEquiv p

/-- The rank-r fiber consists exactly of two r-subsets and a bijection between them. -/
noncomputable def rankEquivCrossPairs (r : ℕ) :
    {p : PartialPairs V W // p.rank = r} ≃ CrossPairs V W r where
  toFun p := p.val.toCrossPairs p.property
  invFun c := ⟨fromCrossPairs c, fromCrossPairs_rank c⟩
  left_inv p := Subtype.ext (from_toCrossPairs p.val p.property)
  right_inv c := fromCrossPairs_injective r (by rw [from_toCrossPairs])

/-- Exact finite partial-bijection fiber cardinality. -/
theorem rank_card (r : ℕ) :
    Fintype.card {p : PartialPairs V W // p.rank = r} =
      (Fintype.card V).choose r * (Fintype.card W).choose r * r.factorial := by
  classical
  rw [Fintype.card_congr (rankEquivCrossPairs (V := V) (W := W) r)]
  exact crossPairs_card V W r

/-- Every vertex on the absorbed/right side has a partner. -/
def FullRight (p : PartialPairs V W) : Prop := ∀ w, ∃ v, p.right w = some v

instance decidableFullRight (p : PartialPairs V W) : Decidable p.FullRight :=
  inferInstanceAs (Decidable (∀ w, ∃ v, p.right w = some v))

/-- Full right coverage is equivalently equality of the right domain with the universe. -/
theorem fullRight_iff_rightDomain (p : PartialPairs V W) :
    p.FullRight ↔ p.rightDomain = Finset.univ := by
  simp only [FullRight, Finset.eq_univ_iff_forall, mem_rightDomain]

/-- Full right coverage is detected exactly by the rank. -/
theorem fullRight_iff_rank (p : PartialPairs V W) :
    p.FullRight ↔ p.rank = Fintype.card W := by
  rw [fullRight_iff_rightDomain]
  change p.rightDomain = Finset.univ ↔ p.leftDomain.card = Fintype.card W
  rw [p.domain_card_eq]
  exact (Finset.card_eq_iff_eq_univ _).symm

/-- The right-to-left partner map of a fully covered right side is injective. -/
noncomputable def toEmbedding (p : PartialPairs V W) (h : p.FullRight) : W ↪ V where
  toFun w := (h w).choose
  inj' := by
    intro w₁ w₂ he
    have h₁ := (p.symm _ _).mpr (h w₁).choose_spec
    have h₂ := (p.symm _ _).mpr (h w₂).choose_spec
    change (h w₁).choose = (h w₂).choose at he
    rw [he] at h₁
    exact Option.some.inj (h₁.symm.trans h₂)

lemma right_toEmbedding (p : PartialPairs V W) (h : p.FullRight) (w : W) :
    p.right w = some (p.toEmbedding h w) := (h w).choose_spec

/-- An injection from the right side determines its inverse partial map on the left. -/
noncomputable def ofEmbedding (f : W ↪ V) : PartialPairs V W := by
  classical
  exact {
    left := fun v => if h : ∃ w, f w = v then some h.choose else none
    right := fun w => some (f w)
    symm := by
      intro v w
      simp only [Option.some.injEq]
      by_cases h : ∃ w, f w = v
      · rw [dif_pos h]
        simp only [Option.some.injEq]
        constructor
        · intro he
          exact he ▸ h.choose_spec
        · intro he
          exact f.injective (h.choose_spec.trans he.symm)
      · rw [dif_neg h]
        simp only [reduceCtorEq, false_iff]
        exact fun he => h ⟨w,he⟩ }

@[simp] lemma ofEmbedding_right (f : W ↪ V) (w : W) :
    (ofEmbedding f).right w = some (f w) := rfl

lemma ofEmbedding_fullRight (f : W ↪ V) : (ofEmbedding f).FullRight :=
  fun w => ⟨f w,rfl⟩

/-- Full absorbed-side coverage is exactly an injection into the surviving side. -/
noncomputable def fullRightEquivEmbedding :
    {p : PartialPairs V W // p.FullRight} ≃ (W ↪ V) where
  toFun p := p.val.toEmbedding p.property
  invFun f := ⟨ofEmbedding f, ofEmbedding_fullRight f⟩
  left_inv p := by
    apply Subtype.ext
    apply ext_right
    funext w
    exact (p.val.right_toEmbedding p.property w).symm
  right_inv f := by
    apply Function.Embedding.ext
    intro w
    apply Option.some.inj
    exact ((ofEmbedding f).right_toEmbedding (ofEmbedding_fullRight f) w).symm

/-- Exact pendant multiplicity for actual partial partner maps. -/
theorem fullRight_card :
    Fintype.card {p : PartialPairs V W // p.FullRight} =
      (Fintype.card V).descFactorial (Fintype.card W) := by
  classical
  rw [Fintype.card_congr (fullRightEquivEmbedding (V := V) (W := W))]
  exact Fintype.card_embedding_eq

/-- The equivalent binomial-times-factorial form of full-right coverage. -/
theorem fullRight_card_choose :
    Fintype.card {p : PartialPairs V W // p.FullRight} =
      (Fintype.card V).choose (Fintype.card W) * (Fintype.card W).factorial := by
  rw [fullRight_card, Nat.descFactorial_eq_factorial_mul_choose]
  ring

end Finite
end PartialPairs
end HiddenCircuits.DH
