import HiddenCircuits.Complexity.BinaryArithmetic.SignedBits
import HiddenCircuits.Complexity.OracleCleanup

/-! A literal destructive nonzero test for canonical signed integers. -/
namespace HiddenCircuits.Approximation.Initialization.SignedNonzero
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic

def state (source out : BitString) : Store 1 := fun r => if r.val=0 then source else out
noncomputable def nonempty : OracleBlock 1 := seq (clear 0) (push 1 true)
noncomputable def magnitude : OracleBlock 1 := branchPop 0 (push 1 false) nonempty nonempty
noncomputable def program : OracleBlock 1 := branchPop 0 (push 1 false) magnitude magnitude

theorem magnitude_executes (g : BitString → ℕ) (xs : BitString) :
    ∃ t, magnitude.Executes g (state xs []) (state [] [decide (xs ≠ [])]) t ∧ t ≤ xs.length+5 := by
  cases xs with
  | nil =>
    refine ⟨3,?_,by simp⟩
    apply branchPop_empty (0 : Fin 2) _ _ _ g rfl
    convert push_executes g (1 : Fin 2) false _ using 1
    funext r;fin_cases r <;> rfl
  | cons b xs =>
    have hc : (clear (0 : Fin 2)).Executes g (state xs []) (state [] []) (xs.length+1) := by
      convert clear_executes g (0 : Fin 2) _ using 1
      funext r;fin_cases r <;> rfl
    have hp : (push (1 : Fin 2) true).Executes g (state [] []) (state [] [true]) 1 := by
      convert push_executes g (1 : Fin 2) true _ using 1
      funext r;fin_cases r <;> rfl
    have hh := seq_executes _ _ g hc hp
    have he : Function.update (state (b::xs) []) 0 xs = state xs [] := by
      funext r;fin_cases r <;> rfl
    refine ⟨xs.length+6,?_,by simp⟩
    cases b
    · convert branchPop_false (0 : Fin 2) _ _ _ g rfl (by rw [he];exact hh) using 1 <;> simp <;> omega
    · convert branchPop_true (0 : Fin 2) _ _ _ g rfl (by rw [he];exact hh) using 1 <;> simp <;> omega

theorem program_executes (g : BitString → ℕ) (z : ℤ) :
    ∃ t, program.Executes g (state (signedBits z) []) (state [] [decide (z ≠ 0)]) t ∧
      t ≤ (signedBits z).length+7 := by
  obtain ⟨t,ht,hb⟩ := magnitude_executes g (Computability.encodeNat z.natAbs)
  have hm : (Computability.encodeNat z.natAbs ≠ []) ↔ z ≠ 0 := by simp [encodeNat_eq_nil_iff]
  simp only [hm] at ht
  have he : Function.update (state (signedBits z) []) 0 (Computability.encodeNat z.natAbs) =
      state (Computability.encodeNat z.natAbs) [] := by
    funext r;fin_cases r <;> rfl
  refine ⟨t+2,?_,by simp only [signedBits,List.length_cons];omega⟩
  cases hsign : negative z
  · apply branchPop_false (0 : Fin 2) _ _ _ g (rest := Computability.encodeNat z.natAbs)
      (by simp [state,signedBits,hsign])
    rw [he]
    exact ht
  · apply branchPop_true (0 : Fin 2) _ _ _ g (rest := Computability.encodeNat z.natAbs)
      (by simp [state,signedBits,hsign])
    rw [he]
    exact ht

theorem program_queryFree : program.QueryFree := by
  have hn : nonempty.QueryFree := seq_queryFree _ _ (clear_queryFree _) (push_queryFree _ _)
  have hm : magnitude.QueryFree := branchPop_queryFree _ _ _ _ (push_queryFree _ _) hn hn
  exact branchPop_queryFree _ _ _ _ (push_queryFree _ _) hm hm

end HiddenCircuits.Approximation.Initialization.SignedNonzero
