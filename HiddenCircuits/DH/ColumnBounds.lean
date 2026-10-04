import HiddenCircuits.DH.PolynomialCounts
import Mathlib.Data.Nat.Size

/-! Counting interpretation of every Q column and explicit binary-size bounds. -/
namespace HiddenCircuits.DH
open Polynomial
open scoped BigOperators
variable {V : Type*} {G : SimpleGraph V} {T : Set V}

def emptyMatching (G : SimpleGraph V) : EncodedMatching G :=
  ⟨fun _ => none,by simp,by simp⟩

lemma bottomMatching_eq_empty (p : EncodedMatching (⊥ : SimpleGraph V)) :
    p = emptyMatching ⊥ := by
  apply Subtype.ext
  funext v
  cases h : p.val v with
  | none => rfl
  | some w => exact (p.property.2 v w h).elim

instance : Subsingleton (EncodedMatching (⊥ : SimpleGraph V)) :=
  ⟨fun p q => (bottomMatching_eq_empty p).trans (bottomMatching_eq_empty q).symm⟩

@[simp] lemma uncovered_emptyMatching [Fintype V] :
    uncovered (emptyMatching G) = Fintype.card V := by
  classical
  simp [uncovered,emptyMatching]

lemma bottom_state_card [Fintype V] (k : ℕ) :
    Fintype.card (BagState (⊥ : SimpleGraph V) Set.univ k) =
      if Fintype.card V = k then 1 else 0 := by
  classical
  by_cases hk : Fintype.card V = k
  · rw [if_pos hk]
    let x : BagState (⊥ : SimpleGraph V) Set.univ k :=
      ⟨emptyMatching ⊥, fun _ _ => Set.mem_univ _, by simp [hk]⟩
    letI : Unique (BagState (⊥ : SimpleGraph V) Set.univ k) := ⟨⟨x⟩,fun y => Subtype.ext (Subsingleton.elim y.val x.val)⟩
    exact Fintype.card_unique
  · rw [if_neg hk]
    haveI : IsEmpty (BagState (⊥ : SimpleGraph V) Set.univ k) := ⟨fun p => by
      have hp := p.property.2
      rw [bottomMatching_eq_empty p.val,uncovered_emptyMatching] at hp
      exact hk hp⟩
    exact Fintype.card_eq_zero

lemma bagPolynomial_bottom [Fintype V] :
    bagPolynomial (⊥ : SimpleGraph V) Set.univ = (X : ℤ[X])^(Fintype.card V) := by
  classical
  ext k
  simp [bagPolynomial_coeff,bottom_state_card,coeff_X_pow,eq_comm]

lemma trueTwinProduct_X_pow (F : ℤ[X]) (j : ℕ) :
    ArrayColumn.trueTwinProduct F (X^j) = matchingColumn F j := by
  simp [ArrayColumn.trueTwinProduct,X_pow_eq_monomial]

/-- Q_j is the actual state polynomial after adjoining j independent active vertices.
Its graph has exactly |V|+j vertices; every old nonactive vertex remains required to be covered. -/
theorem matchingColumn_bag_graph [Fintype V] (j : ℕ) :
    matchingColumn (bagPolynomial G T) j =
      bagPolynomial (joinGraph G (⊥ : SimpleGraph (Fin j)) T Set.univ)
        {x | Sum.elim T Set.univ x} := by
  rw [← trueTwinProduct_X_pow]
  have he : bagPolynomial (⊥ : SimpleGraph (Fin j)) Set.univ = (X : ℤ[X])^j := by
    simpa only [Fintype.card_fin] using (bagPolynomial_bottom (V := Fin j))
  rw [← he]
  exact trueTwinProduct_bag

lemma bagState_card_bound_of_card_le [Fintype V] (n k : ℕ) (hn : Fintype.card V ≤ n) :
    Fintype.card (BagState G T k) ≤ (n+1)^n := by
  calc
    _ ≤ (Fintype.card V+1)^(Fintype.card V) := bagState_card_bound T k
    _ ≤ (n+1)^(Fintype.card V) := Nat.pow_le_pow_left (by omega) _
    _ ≤ (n+1)^n := Nat.pow_le_pow_right (by omega) hn

/-- In particular all Q-column coefficients are nonnegative and have the global graph bound. -/
theorem matchingColumn_bag_coeff_bound [Fintype V] (j k n : ℕ)
    (hn : Fintype.card V+j ≤ n) :
    0 ≤ (matchingColumn (bagPolynomial G T) j).coeff k ∧
      (matchingColumn (bagPolynomial G T) j).coeff k ≤ ((n+1)^n : ℕ) := by
  rw [matchingColumn_bag_graph,bagPolynomial_coeff]
  constructor
  · positivity
  · exact_mod_cast (bagState_card_bound_of_card_le (G := joinGraph G (⊥ : SimpleGraph (Fin j)) T Set.univ)
      (T := {x | Sum.elim T Set.univ x}) n k (by simpa using hn))

/-- A binary length bound with the sharp n log n order, stated using binary size. -/
lemma matchingEnvelope_binary_bound (n : ℕ) :
    (n+1)^n ≤ 2^(n*(n+1).size) := by
  calc
    (n+1)^n ≤ (2^((n+1).size))^n :=
      Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_size_self (n+1))) n
    _ = 2^(n*(n+1).size) := by rw [← pow_mul,Nat.mul_comm]

/-- The magnitude bits of every actual Q coefficient are at most n*size(n+1)+1. -/
theorem matchingColumn_bag_coeff_bits [Fintype V] (j k n : ℕ)
    (hn : Fintype.card V+j ≤ n) :
    ((matchingColumn (bagPolynomial G T) j).coeff k).natAbs.size ≤ n*(n+1).size+1 := by
  obtain ⟨h0,hb⟩ := matchingColumn_bag_coeff_bound (G := G) (T := T) j k n hn
  have hab : ((matchingColumn (bagPolynomial G T) j).coeff k).natAbs ≤ (n+1)^n := by
    have he : (((matchingColumn (bagPolynomial G T) j).coeff k).natAbs : ℤ) =
        (matchingColumn (bagPolynomial G T) j).coeff k := by rw [Int.natCast_natAbs,abs_of_nonneg h0]
    have hb' := hb
    rw [← he] at hb'
    exact_mod_cast hb' 
  have hs := Nat.size_le_size (hab.trans (matchingEnvelope_binary_bound n))
  simpa only [Nat.size_pow] using hs

end HiddenCircuits.DH
