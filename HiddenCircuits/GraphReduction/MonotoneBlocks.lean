import HiddenCircuits.GraphReduction.MonotoneInterleave
import Mathlib.Logic.Equiv.Fin.Basic

namespace HiddenCircuits.GraphReduction

/-- One rank block contains the two original layers, followed by P and Q probe copies. -/
abbrev BlockContent (n s : ℕ) := (Fin n ⊕ Fin n) ⊕ (Fin s ⊕ Fin s)
def endpointBlockWidth (n s : ℕ) : ℕ := 2*n+(s+s)

/-- Each interleaving is an actual injection of all original endpoint labels into its rank interval. -/
def InterleaveMode.embedding {n : ℕ} (m : InterleaveMode n) : (Fin n ⊕ Fin n) ↪ Fin (2*n) where
  toFun
    | .inl u => ⟨m.evenOffset u,m.evenOffset_lt u⟩
    | .inr v => ⟨m.oddOffset v,m.oddOffset_lt v⟩
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (m.evenOffset_injective (congrArg Fin.val h))
      | inr b => exact (m.evenOffset_ne_oddOffset a b (congrArg Fin.val h)).elim
    | inr a =>
      cases b with
      | inl b => exact (m.evenOffset_ne_oddOffset b a (congrArg Fin.val h).symm).elim
      | inr b => exact congrArg Sum.inr (m.oddOffset_injective (congrArg Fin.val h))

/-- The upper-line block order: interleaving, P, Q. -/
def upperBlock {n : ℕ} (m : InterleaveMode n) (s : ℕ) : BlockContent n s ↪ Fin (endpointBlockWidth n s) :=
  (m.embedding.sumMap (finSumFinEquiv.toEmbedding)).trans finSumFinEquiv.toEmbedding

/-- Reorder the four genuine label classes for the lower-line block: Q, interleaving, P. -/
def lowerReorder (n s : ℕ) : BlockContent n s ≃ Fin s ⊕ ((Fin n ⊕ Fin n) ⊕ Fin s) where
  toFun
    | .inl x => .inr (.inl x)
    | .inr (.inl p) => .inr (.inr p)
    | .inr (.inr q) => .inl q
  invFun
    | .inl q => .inr (.inr q)
    | .inr (.inl x) => .inl x
    | .inr (.inr p) => .inr (.inl p)
  left_inv := by intro x; rcases x with (x | (p | q)) <;> rfl
  right_inv := by intro x; rcases x with (q | (x | p)) <;> rfl

/-- The lower-line block order is a genuine finite injection after all adjacent swaps. -/
def lowerBlock {n : ℕ} (m : InterleaveMode n) (s : ℕ) : BlockContent n s ↪ Fin (endpointBlockWidth n s) := by
  let tail : ((Fin n ⊕ Fin n) ⊕ Fin s) ↪ Fin (2*n+s) :=
    (m.embedding.sumMap (Function.Embedding.refl _)).trans finSumFinEquiv.toEmbedding
  let whole : (Fin s ⊕ ((Fin n ⊕ Fin n) ⊕ Fin s)) ↪ Fin (s+(2*n+s)) :=
    ((Function.Embedding.refl _).sumMap tail).trans finSumFinEquiv.toEmbedding
  exact (lowerReorder n s).toEmbedding.trans
    (whole.trans ⟨Fin.cast (by unfold endpointBlockWidth; omega),Fin.cast_injective _⟩)

@[simp] theorem upperBlock_even {n s : ℕ} (m : InterleaveMode n) (u : Fin n) :
    (upperBlock m s (.inl (.inl u))).val=m.evenOffset u := rfl
@[simp] theorem upperBlock_odd {n s : ℕ} (m : InterleaveMode n) (v : Fin n) :
    (upperBlock m s (.inl (.inr v))).val=m.oddOffset v := rfl
@[simp] theorem upperBlock_P {n s : ℕ} (m : InterleaveMode n) (t : Fin s) :
    (upperBlock m s (.inr (.inl t))).val=2*n+t.val := rfl
@[simp] theorem upperBlock_Q {n s : ℕ} (m : InterleaveMode n) (t : Fin s) :
    (upperBlock m s (.inr (.inr t))).val=2*n+(s+t.val) := rfl
@[simp] theorem lowerBlock_even {n s : ℕ} (m : InterleaveMode n) (u : Fin n) :
    (lowerBlock m s (.inl (.inl u))).val=s+m.evenOffset u := rfl
@[simp] theorem lowerBlock_odd {n s : ℕ} (m : InterleaveMode n) (v : Fin n) :
    (lowerBlock m s (.inl (.inr v))).val=s+m.oddOffset v := rfl
@[simp] theorem lowerBlock_P {n s : ℕ} (m : InterleaveMode n) (t : Fin s) :
    (lowerBlock m s (.inr (.inl t))).val=s+(2*n+t.val) := rfl
@[simp] theorem lowerBlock_Q {n s : ℕ} (m : InterleaveMode n) (t : Fin s) :
    (lowerBlock m s (.inr (.inr t))).val=t.val := rfl

/-- Integer ranks of separated endpoint blocks. -/
def digitRank {B L : ℕ} (x : Fin B × Fin L) : ℕ := x.1.val*L+x.2.val

 theorem digitRank_lt_of_block_lt {B L : ℕ} (x y : Fin B × Fin L) (h : x.1.val<y.1.val) :
    digitRank x < digitRank y := by
  have hc := Nat.mul_le_mul_right L (Nat.succ_le_iff.mpr h)
  have hx := x.2.isLt
  unfold digitRank
  nlinarith

 theorem digitRank_lt_iff {B L : ℕ} (x y : Fin B × Fin L) :
    digitRank x < digitRank y ↔
      x.1.val<y.1.val ∨ (x.1.val=y.1.val ∧ x.2.val<y.2.val) := by
  constructor
  · intro h
    by_cases hl : x.1.val<y.1.val
    · exact Or.inl hl
    by_cases hr : y.1.val<x.1.val
    · exact (Nat.lt_asymm h (digitRank_lt_of_block_lt y x hr)).elim
    have he : x.1.val=y.1.val := by omega
    refine Or.inr ⟨he,?_⟩
    unfold digitRank at h
    rw [he] at h
    omega
  · rintro (hl | ⟨he,hl⟩)
    · exact digitRank_lt_of_block_lt x y hl
    · unfold digitRank
      rw [he]
      omega

 theorem digitRank_injective {B L : ℕ} : Function.Injective (digitRank (B:=B) (L:=L)) := by
  intro x y h
  have he : x.1.val=y.1.val := by
    by_contra hn
    rcases Nat.lt_or_gt_of_ne hn with hlt | hgt
    · have hh := digitRank_lt_of_block_lt x y hlt
      omega
    · have hh := digitRank_lt_of_block_lt y x hgt
      omega
  have ht : x.2.val=y.2.val := by
    unfold digitRank at h
    rw [he] at h
    omega
  exact Prod.ext (Fin.ext he) (Fin.ext ht)

end HiddenCircuits.GraphReduction
