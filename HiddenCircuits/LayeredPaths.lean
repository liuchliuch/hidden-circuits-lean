import HiddenCircuits.CutMatching

/-! Concrete paths of states and permitted cut bijections, counted by transfer products. -/
namespace HiddenCircuits
open scoped BigOperators

/-- An explicitly unweighted cut matrix. -/
abbrev UnweightedCut (p : ℕ) := Fin (2*p) → Fin (2*p) → Bool

/-- The zero-one rational biadjacency matrix of a literal Boolean cut. -/
def cutMatrix {p : ℕ} (R : UnweightedCut p) : Matrix (Fin (2*p)) (Fin (2*p)) ℚ :=
  fun i j => if R i j then 1 else 0

/-- A selected permutation is exactly an edge bijection across the specified cut. -/
def CutPermutation {p : ℕ} (R : UnweightedCut p) (S T : State (2*p) p) :=
  {σ : Equiv.Perm (Fin p) // ∀ j, R (S.track (σ j)) (T.halfComplement.track j) = true}

instance {p : ℕ} (R : UnweightedCut p) (S T : State (2*p) p) : Fintype (CutPermutation R S T) := by
  unfold CutPermutation
  infer_instance

 theorem cutPermutation_card {p : ℕ} (R : UnweightedCut p) (S T : State (2*p) p) :
    (Fintype.card (CutPermutation R S T) : ℚ) = layerTransfer (cutMatrix R) S T := by
  rw [layerTransfer_apply]
  rw [Fintype.card_congr (show CutPermutation R S T ≃
    {σ : Equiv.Perm (Fin p) // ∀ j, R (S.track (σ j)) (T.halfComplement.track j) = true}
    from Equiv.refl _)]
  change _ = Matrix.permanent (fun i j =>
    if R (S.track i) (T.halfComplement.track j) = true then (1 : ℚ) else 0)
  convert (permanent_indicator_count
    (fun i j => R (S.track i) (T.halfComplement.track j) = true)).symm using 1 <;> congr!

/-- A complete state path includes its actual permitted bijection at each cut. -/
def TransferPath {p : ℕ} : List (UnweightedCut p) → State (2*p) p → State (2*p) p → Type
  | [], S,T => PLift (S=T)
  | R::w, S,T => Σ U : State (2*p) p, CutPermutation R S U × TransferPath w U T

noncomputable instance transferPathFintype {p : ℕ} :
    (w : List (UnweightedCut p)) → (S T : State (2*p) p) → Fintype (TransferPath w S T)
  | [], S,T => by classical exact inferInstanceAs (Fintype (PLift (S=T)))
  | R::w, S,T => by
    classical
    letI := fun U => transferPathFintype w U T
    exact inferInstanceAs (Fintype (Σ U : State (2*p) p, CutPermutation R S U × TransferPath w U T))

/-- The ordinary product of the actual consecutive cut transfers. -/
def transferProduct {p : ℕ} (w : List (UnweightedCut p)) :
    Matrix (State (2*p) p) (State (2*p) p) ℚ :=
  (w.map (fun R => layerTransfer (cutMatrix R))).prod

@[simp] theorem transferProduct_nil (p : ℕ) : transferProduct (p:=p) [] = 1 := rfl
@[simp] theorem transferProduct_cons {p : ℕ} (R : UnweightedCut p) (w : List (UnweightedCut p)) :
    transferProduct (R::w) = layerTransfer (cutMatrix R) * transferProduct w := rfl

/-- Matrix multiplication counts all actual intermediate states and cut bijections,
including the forced complementary set on the later side of each cut. -/
theorem transferPath_card {p : ℕ} (w : List (UnweightedCut p)) (S T : State (2*p) p) :
    (Fintype.card (TransferPath w S T) : ℚ) = transferProduct w S T := by
  induction w generalizing S with
  | nil =>
    change (Fintype.card (PLift (S=T)) : ℚ) = (1 : Matrix _ _ ℚ) S T
    by_cases h : S=T
    · subst T
      simp
    · simp [h]
  | cons R w ih =>
    change (Fintype.card (Σ U : State (2*p) p, CutPermutation R S U × TransferPath w U T) : ℚ) = _
    simp only [Fintype.card_sigma,Fintype.card_prod,Nat.cast_sum,Nat.cast_mul,
      cutPermutation_card,ih,transferProduct_cons,Matrix.mul_apply]

end HiddenCircuits
