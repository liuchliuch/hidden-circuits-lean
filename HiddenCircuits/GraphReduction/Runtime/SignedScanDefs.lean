import HiddenCircuits.Complexity.BinaryArithmetic.StraightLine
import HiddenCircuits.Complexity.MatrixEmitterRows

/-! Concrete clean arithmetic-bank states and finite signed flags.
The callback parameters are physically framed below stack 80. -/
namespace HiddenCircuits.GraphReduction.Runtime
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic RegisterMachine

namespace SignedCounter

def value (bits : Bool × Bool) : ℤ := if bits.1 then 1 else if bits.2 then -1 else 0
lemma value_abs (bits : Bool × Bool) : (value bits).natAbs ≤ 1 := by
  rcases bits with ⟨a,b⟩; cases a <;> cases b <;> decide

def counterBound (C n : ℕ) : ℕ := C+n+3
lemma bounded_counter (R : Fin 7 → ℤ) (C n : ℕ) (d : ℤ)
    (hR : Bounded C R) (hd : d.natAbs ≤ n) :
    Bounded (counterBound C n) (Function.update R 2 (R 2+d)) := by
  intro q
  by_cases hq : q=2
  · subst q
    simp only [Function.update_self]
    have hpow : d.natAbs ≤ 2^n := hd.trans (Nat.le_of_lt Nat.lt_two_pow_self)
    exact signedBits_length_of_abs_bound (add_abs_envelope C n (R 2) d
      (abs_le_pow_signed_length _ _ (hR 2)) hpow)
  · simp only [Function.update_of_ne hq]
    exact (hR q).trans (by unfold counterBound; omega)
end SignedCounter

namespace SignedScan

def state (n i j : ℕ) (bits out inner outer : BitString) (params : Store 95)
    (R : Fin 7 → ℤ) : Store 95 := fun q =>
  if h : 80 ≤ q.val then
    RegisterMachine.store [] [] (signedBits ∘ R) ⟨q.val-80,by omega⟩
  else MatrixEmitter.store n i j bits out inner outer params q

def arithmeticMap : Fin 16 ↪ Fin 96 where
  toFun q := ⟨80+q.val,by omega⟩
  inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega

@[simp] lemma state_arithmetic (n i j : ℕ) (bits out inner outer : BitString)
    (params : Store 95) (R : Fin 7 → ℤ) (q : Fin 16) :
    state n i j bits out inner outer params R (arithmeticMap q)=
      RegisterMachine.store [] [] (signedBits ∘ R) q := by
  simp [state,arithmeticMap]

@[simp] lemma state_core (n i j : ℕ) (bits out inner outer : BitString)
    (params : Store 95) (R : Fin 7 → ℤ) (q : Fin 8) :
    state n i j bits out inner outer params R (MatrixEmitter.port q)=
      (![List.replicate n true,List.replicate i true,List.replicate j true,bits,out,inner,outer,[]] : Fin 8 → BitString) q := by
  have hq : ¬80 ≤ (MatrixEmitter.port (k:=88) q).val := by simp [MatrixEmitter.port]; omega
  simp only [state,hq,↓reduceDIte,MatrixEmitter.store_core]

lemma update_bits (n i j : ℕ) (bits out inner outer next : BitString)
    (params : Store 95) (R : Fin 7 → ℤ) :
    Function.update (state n i j bits out inner outer params R) (3 : Fin 96) next=
      state n i j next out inner outer params R := by
  funext q
  by_cases hq : q=3
  · subst q; rfl
  · simp only [Function.update_of_ne hq,state]
    split_ifs with h
    · rfl
    · simp [MatrixEmitter.store,Function.update_apply,MatrixEmitter.port] at *
      split_ifs <;> simp_all

lemma update_inner (n i j : ℕ) (bits out inner outer next : BitString)
    (params : Store 95) (R : Fin 7 → ℤ) :
    Function.update (state n i j bits out inner outer params R) (5 : Fin 96) next=
      state n i j bits out next outer params R := by
  funext q
  by_cases hq : q=5
  · subst q; rfl
  · simp only [Function.update_of_ne hq,state]
    split_ifs with h
    · rfl
    · exact (Function.update_of_ne hq _ _).symm.trans (congrFun (MatrixEmitter.store_inner n i j bits out inner outer next params) q)

lemma update_column (n i j : ℕ) (bits out inner outer : BitString)
    (params : Store 95) (R : Fin 7 → ℤ) :
    Function.update (state n i j bits out inner outer params R) (2 : Fin 96) (true::List.replicate j true)=
      state n i (j+1) bits out inner outer params R := by
  funext q
  by_cases hq : q=2
  · subst q; simp [state,MatrixEmitter.store,MatrixEmitter.port,List.replicate_succ]
  · simp only [Function.update_of_ne hq,state]
    split_ifs with h
    · rfl
    · exact (Function.update_of_ne hq _ _).symm.trans (congrFun (MatrixEmitter.store_column n i j bits out inner outer params) q)

lemma clear_column (n i j : ℕ) (bits out inner outer : BitString)
    (params : Store 95) (R : Fin 7 → ℤ) :
    Function.update (state n i j bits out inner outer params R) (2 : Fin 96) []=
      state n i 0 bits out inner outer params R := by
  funext q
  by_cases hq : q=2
  · subst q; rfl
  · simp only [Function.update_of_ne hq,state]
    split_ifs with h
    · rfl
    · exact (Function.update_of_ne hq _ _).symm.trans (congrFun (MatrixEmitter.store_column_zero n i j bits out inner outer params) q)

def total (edge : ℕ → ℕ → Bool × Bool) (i : ℕ) : ℕ → ℕ → ℤ
  | _,0 => 0
  | j,m+1 => SignedCounter.value (edge i j)+total edge i (j+1) m

lemma total_abs (edge : ℕ → ℕ → Bool × Bool) (i j m : ℕ) : (total edge i j m).natAbs ≤ m := by
  induction m generalizing j with
  | zero => simp [total]
  | succ m ih =>
    exact (Int.natAbs_add_le _ _).trans (by have := SignedCounter.value_abs (edge i j); have := ih (j+1); omega)

end SignedScan
end HiddenCircuits.GraphReduction.Runtime
