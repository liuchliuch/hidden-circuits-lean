import HiddenCircuits.Complexity.BinaryArithmetic.Factorial

/-! Unary-to-binary conversion by literal pops and binary ripple increments. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic
open OracleBlock

def unaryBinaryStore (clock counter scratch : BitString) : Store 2 :=
  fun i => if i.val=0 then clock else if i.val=1 then counter else scratch

def unaryIncrementEmbedding : Fin 2 ↪ Fin 3 where
  toFun i := if i=0 then 1 else 2
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

noncomputable def unaryIncrement : OracleBlock 2 := rename incrementBlock unaryIncrementEmbedding
noncomputable def unaryBinary : OracleBlock 2 := whilePop 0 unaryIncrement unaryIncrement

def unaryBinaryCost (k : ℕ) : ℕ → ℕ
  | 0 => 1
  | r+1 => 4*BitPrograms.leadingOnes (Computability.encodeNat k)+5+unaryBinaryCost (k+1) r

 theorem unaryIncrement_executes (g : BitString → ℕ) (clock : BitString) (k : ℕ) :
    unaryIncrement.Executes g (unaryBinaryStore clock (Computability.encodeNat k) [])
      (unaryBinaryStore clock (Computability.encodeNat (k+1)) [])
      (4*BitPrograms.leadingOnes (Computability.encodeNat k)+3) := by
  apply rename_executes_to incrementBlock unaryIncrementEmbedding g (incrementBlock_executes g (Computability.encodeNat k))
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i
    · exact (BitPrograms.increment_encodeNat k).symm
    · rfl
  · intro i hi; fin_cases i <;> first | rfl | (exfalso; exact hi 0 rfl)

 theorem unaryBinary_executes (g : BitString → ℕ) (clock : BitString) (k : ℕ) :
    unaryBinary.Executes g (unaryBinaryStore clock (Computability.encodeNat k) [])
      (unaryBinaryStore [] (Computability.encodeNat (k+clock.length)) []) (unaryBinaryCost k clock.length) := by
  apply whilePop_executes
  induction clock generalizing k with
  | nil =>
    simpa [unaryBinaryCost] using (WhileExecution.empty (unaryBinaryStore [] (Computability.encodeNat k) []) rfl)
  | cons bit rest ih =>
    have hs : Function.update (unaryBinaryStore (bit::rest) (Computability.encodeNat k) []) 0 rest =
        unaryBinaryStore rest (Computability.encodeNat k) [] := by funext i; fin_cases i <;> rfl
    have hb := unaryIncrement_executes g rest k
    rw [← hs] at hb
    cases bit
    · have h := WhileExecution.zero rfl hb (ih (k+1))
      convert h using 1 <;> simp only [unaryBinaryCost,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] <;> omega
    · have h := WhileExecution.one rfl hb (ih (k+1))
      convert h using 1 <;> simp only [unaryBinaryCost,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] <;> omega

 theorem unaryBinaryCost_le (r k n : ℕ) (h : k+r ≤ n) :
    unaryBinaryCost k r ≤ 1+r*(4*n+5) := by
  induction r generalizing k with
  | zero => simp [unaryBinaryCost]
  | succ r ih =>
    have ht := ih (k+1) (by omega)
    have hb := BitPrograms.leadingOnes_le_length (Computability.encodeNat k)
    have hs : (Computability.encodeNat k).length ≤ k := by
      rw [encodeNat_length]; exact Nat.size_le.mpr Nat.lt_two_pow_self
    simp only [unaryBinaryCost]
    nlinarith

lemma unaryBinary_queryFree : unaryBinary.QueryFree :=
  whilePop_queryFree _ _ _ (rename_queryFree _ _ factorialIncrement_queryFree)
    (rename_queryFree _ _ factorialIncrement_queryFree)

end HiddenCircuits.Complexity.BinaryArithmetic
