import HiddenCircuits.Complexity.DeterminantRuntime.IdentityMatrix
import HiddenCircuits.Complexity.DeterminantRuntime.RoundLayout

/-! Actual identity matrix, signed-one coefficient, and unary outer-clock setup. -/
namespace HiddenCircuits.Complexity.DeterminantRuntime.Prepare
open OracleBlock BinaryArithmetic

def identityPorts : Fin 25 ↪ Fin 31 where
  toFun := ![0,10,11,12,13,14,15,2,1,3,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30]
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

noncomputable def program : OracleBlock 30 := seq (IdentityMatrix.on identityPorts)
  (seq (push 3 true) (seq (push 3 false) (copyOn 0 5 10 (by decide) (by decide) (by decide))))

theorem executes (g : BitString → ℕ) (n : ℕ) (a : BitString) :
    ∃ t, program.Executes g (Round.store n a [] [] 0 0)
      (Round.store n a (encodeBitList (matrixWords (1 : Matrix (Fin n) (Fin n) ℤ))) (signedBits 1) 0 n) t ∧
      t ≤ IdentityMatrix.time.eval n+5*n+10 := by
  let ident := encodeBitList (matrixWords (1 : Matrix (Fin n) (Fin n) ℤ))
  obtain ⟨t,ht,hb⟩ := IdentityMatrix.on_executes identityPorts g n a [] (Round.store n a [] [] 0 0)
    (by funext q; fin_cases q <;> rfl)
  have he : Function.update (Round.store n a [] [] 0 0) (identityPorts 7) ident = Round.store n a ident [] 0 0 := by
    funext q; fin_cases q <;> rfl
  change (IdentityMatrix.on identityPorts).Executes g _ (Function.update _ _ ident) t at ht
  rw [he] at ht
  have h1 : (push (3 : Fin 31) true).Executes g (Round.store n a ident [] 0 0)
      (Round.store n a ident [true] 0 0) 1 := by
    convert push_executes g (3 : Fin 31) true (Round.store n a ident [] 0 0) using 1
    funext q; fin_cases q <;> rfl
  have h2 : (push (3 : Fin 31) false).Executes g (Round.store n a ident [true] 0 0)
      (Round.store n a ident (signedBits 1) 0 0) 1 := by
    convert push_executes g (3 : Fin 31) false (Round.store n a ident [true] 0 0) using 1
    funext q; fin_cases q <;> rfl
  have h3 : (copyOn (0 : Fin 31) 5 10 (by decide) (by decide) (by decide)).Executes g
      (Round.store n a ident (signedBits 1) 0 0) (Round.store n a ident (signedBits 1) 0 n) (5*n+2) := by
    have h := copyOn_executes g (0 : Fin 31) 5 10 (by decide) (by decide) (by decide)
      (Round.store n a ident (signedBits 1) 0 0) rfl
    have he : Function.update (Round.store n a ident (signedBits 1) 0 0) 5 (List.replicate n true) =
        Round.store n a ident (signedBits 1) 0 n := by funext q; fin_cases q <;> rfl
    simpa only [show Round.store n a ident (signedBits 1) 0 0 0 = List.replicate n true from rfl,
      show Round.store n a ident (signedBits 1) 0 0 5 = [] from rfl,List.append_nil,List.length_replicate,he] using h
  exact ⟨_,seq_executes _ _ g ht (seq_executes _ _ g h1 (seq_executes _ _ g h2 h3)),by omega⟩

theorem queryFree : program.QueryFree := seq_queryFree _ _ (IdentityMatrix.on_queryFree _)
  (seq_queryFree _ _ (push_queryFree _ _) (seq_queryFree _ _ (push_queryFree _ _) (copyOn_queryFree _ _ _ _ _ _)))

end HiddenCircuits.Complexity.DeterminantRuntime.Prepare
