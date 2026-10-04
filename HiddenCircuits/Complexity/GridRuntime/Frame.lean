import HiddenCircuits.Complexity.GridRuntime.Prefix

/-! Arbitrary caller-stack embedding and untouched off-image data for the grid engine. -/
namespace HiddenCircuits.Complexity.GridRuntime
open OracleBlock
variable {k l : ℕ}

noncomputable def programOn (B : OracleBlock (k+8)) (φ : Fin ((k+8)+1) ↪ Fin (l+1)) : OracleBlock l :=
  rename (program B) φ

theorem programOn_executes (B : OracleBlock (k+8)) (φ : Fin ((k+8)+1) ↪ Fin (l+1))
    (g : BitString → ℕ) (n m C : ℕ) (states : ℕ → ℕ → Frame k)
    (hB : BodySpec B g n m C states) (hrow : ∀ i, i≤n → states i (m+1)=states (i+1) 0)
    (s t : Store l) (hs : s∘φ=initialStore n m (states 0 0))
    (ht : t∘φ=initialStore n m (states (n+1) 0))
    (hframe : ∀ j, (∀ i, φ i≠j) → t j=s j) :
    ∃ c, (programOn B φ).Executes g s t c ∧ c≤programCost n m C := by
  obtain ⟨c,hc,hcb⟩ := program_executes B g n m C states hB hrow
  exact ⟨c,rename_executes_to (program B) φ g hc hs ht hframe,hcb⟩

theorem programOn_queryFree (B : OracleBlock (k+8)) (φ : Fin ((k+8)+1) ↪ Fin (l+1))
    (hB : B.QueryFree) : (programOn B φ).QueryFree := rename_queryFree _ _ (program_queryFree B hB)
end HiddenCircuits.Complexity.GridRuntime
