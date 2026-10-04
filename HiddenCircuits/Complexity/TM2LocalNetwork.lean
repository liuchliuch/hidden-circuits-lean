import HiddenCircuits.Complexity.TM2Ports
import HiddenCircuits.Complexity.LocalCompletion
import HiddenCircuits.Complexity.TM2BooleanTableau

/-! Construct the actual fixed-width Boolean network for a finite TM2 verifier.
Height-dependent vertex numbering is explicit arithmetic; all chosen finite
enumerations depend only on the fixed machine. -/
namespace HiddenCircuits.Complexity.TM2BooleanEncoding

abbrev Symbols (M : Turing.FinTM2) := (k : M.K) × Option (Symbol M k)
noncomputable instance symbolsFintype (M : Turing.FinTM2) : Fintype (Symbols M) := by
  letI := M.kFin
  infer_instance

lemma symbols_card (M : Turing.FinTM2) : Fintype.card (Symbols M) = symbolBits M := by
  letI := M.kFin
  simp [Symbols,symbolBits,Fintype.card_sigma]

noncomputable def symbolEnumeration (M : Turing.FinTM2) : Symbols M ≃ Fin (symbolBits M) :=
  (Fintype.equivFin (Symbols M)).trans (finCongr (symbols_card M))

def cellSplit (M : Turing.FinTM2) (height : ℕ) :
    Cell M height ≃ Control M ⊕ (Fin height × Symbols M) where
  toFun
    | .inl q => .inl q
    | .inr ⟨k,(i,a)⟩ => .inr (i,⟨k,a⟩)
  invFun
    | .inl q => .inl q
    | .inr (i,⟨k,a⟩) => .inr ⟨k,(i,a)⟩
  left_inv c := by cases c with
    | inl q => rfl
    | inr c => rcases c with ⟨k,i,a⟩; rfl
  right_inv c := by cases c with
    | inl q => rfl
    | inr c => rcases c with ⟨i,k,a⟩; rfl

noncomputable def bitCount (M : Turing.FinTM2) (height : ℕ) : ℕ := controlBits M+height*symbolBits M

/-- Only the two machine-constant symbol/control alphabets need enumerations.
Products and sums handle the variable height explicitly. -/
noncomputable def cellEnumeration (M : Turing.FinTM2) (height : ℕ) : Cell M height ≃ Fin (bitCount M height) :=
  (cellSplit M height).trans
    ((Equiv.sumCongr (Fintype.equivFin (Control M))
      (((Equiv.refl (Fin height)).prodCongr (symbolEnumeration M)).trans finProdFinEquiv)).trans
      finSumFinEquiv)

noncomputable def portEnumeration (M : Turing.FinTM2) : Port M ≃ Fin (Fintype.card (Port M)) :=
  Fintype.equivFin (Port M)

noncomputable def encodedPorts (M : Turing.FinTM2) (height : ℕ)
    (i : Fin (bitCount M height)) (p : Fin (Fintype.card (Port M))) : Fin (bitCount M height) :=
  cellEnumeration M height (portCell M height
    (cellIndex M ((cellEnumeration M height).symm i)) ((portEnumeration M).symm p))

noncomputable def encodedStep (M : Turing.FinTM2) (height : ℕ)
    (w : Fin (bitCount M height) → Bool) (i : Fin (bitCount M height)) : Bool :=
  stepCode M height (fun c => w (cellEnumeration M height c)) ((cellEnumeration M height).symm i)

/-- All local rules are constructed from the actual transition and its proved port set. -/
noncomputable def network (M : Turing.FinTM2) (height : ℕ) :
    LocalNetwork (bitCount M height) (Fintype.card (Port M)) :=
  compileLocal (encodedStep M height) (encodedPorts M height)

theorem network_step (M : Turing.FinTM2) (height : ℕ) (w : Fin (bitCount M height) → Bool) :
    (network M height).step w = encodedStep M height w := by
  apply compileLocal_correct
  intro i w z h
  apply stepCode_depends_ports
  intro p
  have hp := h (portEnumeration M p)
  simpa [encodedPorts] using hp

noncomputable def encodeFin (M : Turing.FinTM2) (height : ℕ) (c : M.Cfg) :
    Fin (bitCount M height) → Bool :=
  fun i => encode M height c ((cellEnumeration M height).symm i)

/-- The fully constructed Boolean network simulates one actual macrostep. -/
theorem network_step_encode (M : Turing.FinTM2) (height : ℕ) (c : M.Cfg) (hc : Valid M height c) :
    (network M height).step (encodeFin M height c) = encodeFin M height (stutter M.step c) := by
  rw [network_step]
  have he : (fun cell => encodeFin M height c (cellEnumeration M height cell)) = encode M height c := by
    funext cell
    simp [encodeFin]
  funext i
  unfold encodedStep
  rw [he,stepCode_encode M height c hc]
  rfl

/-- A complete bounded execution is represented with no assumed transition circuit. -/
theorem network_iterate_input (M : Turing.FinTM2) (x : List (M.Γ M.k₀)) (T t : ℕ) (ht : t ≤ T) :
    ((network M (x.length+T*TM2Space.machineBudget M)).step)^[t]
      (encodeFin M (x.length+T*TM2Space.machineBudget M) (Turing.initList M x)) =
    encodeFin M (x.length+T*TM2Space.machineBudget M)
      ((stutter M.step)^[t] (Turing.initList M x)) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',ih (by omega)]
    exact network_step_encode _ _ _ (input_valid_at_horizon M x t T (by omega))

end HiddenCircuits.Complexity.TM2BooleanEncoding
