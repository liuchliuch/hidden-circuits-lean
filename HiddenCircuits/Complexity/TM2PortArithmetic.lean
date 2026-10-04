import HiddenCircuits.Complexity.TM2FiniteRuleTable

/-! Scalar addresses for the actual encoded TM2 ports, and finite boundary
classification of every address guard. -/
namespace HiddenCircuits.Complexity.TM2BooleanEncoding
attribute [local instance] Classical.propDecidable

lemma cellEnumeration_control_val (M : Turing.FinTM2) (H : ℕ) (q : Control M) :
    (cellEnumeration M H (Sum.inl q)).val = (Fintype.equivFin (Control M) q).val := rfl

lemma cellEnumeration_stack_val (M : Turing.FinTM2) (H : ℕ) (k : M.K)
    (i : Fin H) (s : Option (Symbol M k)) :
    (cellEnumeration M H (Sum.inr ⟨k,(i,s)⟩)).val =
      controlBits M+i.val*symbolBits M+(symbolEnumeration M ⟨k,s⟩).val := by
  change controlBits M+((symbolEnumeration M ⟨k,s⟩).val+symbolBits M*i.val) = _
  ring

noncomputable def controlIndex (M : Turing.FinTM2) (q : Control M) : ℕ := (Fintype.equivFin (Control M) q).val
noncomputable def symbolIndex (M : Turing.FinTM2) (k : M.K) (s : Option (Symbol M k)) : ℕ :=
  (symbolEnumeration M ⟨k,s⟩).val

noncomputable def portAddress (M : Turing.FinTM2) (H j : ℕ) : Port M → ℕ
  | .inl q => controlIndex M q
  | .inr ⟨k,(p,s)⟩ =>
    if portPosition M j p < H then controlBits M+portPosition M j p*symbolBits M+symbolIndex M k s
    else controlIndex M (none,M.initialState)

/-- This is the actual scalar variable index, not an abstract size surrogate. -/
theorem portAddress_correct (M : Turing.FinTM2) (H j : ℕ) (p : Port M) :
    portAddress M H j p = (cellEnumeration M H (portCell M H j p)).val := by
  cases p with
  | inl q => rfl
  | inr p =>
    rcases p with ⟨k,p,s⟩
    simp only [portAddress,portCell]
    split_ifs with h
    · exact (cellEnumeration_stack_val M H k ⟨portPosition M j p,h⟩ s).symm
    · rfl

lemma portPosition_cap_valid (M : Turing.FinTM2) (j r : ℕ) (p : Position M) :
    portPosition M j p < j+r+1 ↔
      portPosition M (min j (2*inspectionConstant M)) p <
        min j (2*inspectionConstant M)+min r (2*inspectionConstant M)+1 := by
  cases p with
  | inl i =>
    simp only [portPosition]
    have hi := i.isLt
    omega
  | inr ab =>
    rcases ab with ⟨a,b⟩
    exact cap_shift_lt_iff (by have := a.isLt;omega) (by have := b.isLt;omega)

/-- Address range tests can be selected by a fixed finite table of capped left
and right distances, independently of the total height. -/
noncomputable def portValidTable (M : Turing.FinTM2) (j r : Fin (2*inspectionConstant M+1))
    (p : Position M) : Bool := decide (portPosition M j.val p < j.val+r.val+1)

theorem portValidTable_correct (M : Turing.FinTM2) (j r : ℕ) (p : Position M) :
    portValidTable M (cappedPosition M j) (cappedPosition M r) p = decide (portPosition M j p < j+r+1) := by
  apply decide_eq_decide.mpr
  exact (portPosition_cap_valid M j r p).symm

end HiddenCircuits.Complexity.TM2BooleanEncoding
