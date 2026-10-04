import HiddenCircuits.Complexity.DeterminantRuntime.RoundLayout
import HiddenCircuits.Complexity.DeterminantRuntime.Negation
import HiddenCircuits.Complexity.BinaryArithmetic.Parity

/-! Actual unary parity scan and canonical final determinant sign correction. -/
namespace HiddenCircuits.Complexity.DeterminantRuntime.Sign
open OracleBlock BinaryArithmetic

def parityPorts : Fin 2 ↪ Fin 31 where
  toFun := ![10,11]
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

noncomputable def select : OracleBlock 30 := branchPop 11 skip skip (Negation.negateOn 3)
noncomputable def program : OracleBlock 30 := seq (copyOn 0 10 12 (by decide) (by decide) (by decide))
  (seq (rename parityBlock parityPorts) select)

theorem select_executes (g : BitString → ℕ) (n : ℕ) (a b : BitString) (c : ℤ) (k clock : ℕ) :
    ∃ t, select.Executes g (Function.update (Round.store n a b (signedBits c) k clock) 11 [parityBit n])
      (Round.store n a b (signedBits ((-1)^n*c)) k clock) t ∧ t ≤ 7 := by
  let s := Round.store n a b (signedBits c) k clock
  have hp : Function.update (Function.update s (11 : Fin 31) [parityBit n]) 11 [] = s := by
    rw [Function.update_idem]
    exact Function.update_eq_self _ _
  have he : (-1 : ℤ)^n = signedNat (parityBit n) 1 := (signedNat_parity n).symm
  cases hn : parityBit n with
  | false =>
    have ht : Round.store n a b (signedBits ((-1)^n*c)) k clock = s := by
      simp [he,hn,signedNat,s]
    rw [ht]
    refine ⟨3,?_,by omega⟩
    rw [hn] at hp
    apply branchPop_false (11 : Fin 31) skip skip (Negation.negateOn 3) g (rest := []) rfl
    rw [hp]
    exact skip_executes g s
  | true =>
    obtain ⟨t,ht,hb⟩ := Negation.negateOn_executes g (3 : Fin 31) s c rfl
    have hout : Function.update s 3 (signedBits (-c)) = Round.store n a b (signedBits ((-1)^n*c)) k clock := by
      simp only [he,hn,signedNat,ite_true,Int.natCast_one,neg_mul,one_mul]
      funext q; fin_cases q <;> rfl
    rw [hout] at ht
    refine ⟨t+2,?_,by omega⟩
    rw [hn] at hp
    apply branchPop_true (11 : Fin 31) skip skip (Negation.negateOn 3) g (rest := []) rfl
    rw [hp]
    exact ht

theorem executes (g : BitString → ℕ) (n : ℕ) (a b : BitString) (c : ℤ) (k clock : ℕ) :
    ∃ t, program.Executes g (Round.store n a b (signedBits c) k clock)
      (Round.store n a b (signedBits ((-1)^n*c)) k clock) t ∧ t ≤ 6*n+15 := by
  let s := Round.store n a b (signedBits c) k clock
  let s1 := Function.update s (10 : Fin 31) (List.replicate n true)
  let s2 := Function.update s (11 : Fin 31) [parityBit n]
  have h1 : (copyOn (0 : Fin 31) 10 12 (by decide) (by decide) (by decide)).Executes g s s1 (5*n+2) := by
    simpa only [show s 0 = List.replicate n true from rfl, show s 10 = [] from rfl,
      List.append_nil,List.length_replicate] using copyOn_executes g (0 : Fin 31) 10 12
        (by decide) (by decide) (by decide) s rfl
  have h2 : (rename parityBlock parityPorts).Executes g s1 s2 (n+2) := by
    have h := parityBlock_executes g (List.replicate n true) []
    simp only [List.length_replicate] at h
    apply rename_executes_to parityBlock parityPorts g h
    · funext q; fin_cases q <;> rfl
    · funext q; fin_cases q <;> rfl
    · intro q hq; fin_cases q <;> first | exact (hq 0 rfl).elim | exact (hq 1 rfl).elim | rfl
  obtain ⟨t,ht,hb⟩ := select_executes g n a b c k clock
  exact ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 ht),by omega⟩

theorem queryFree : program.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (rename_queryFree _ _ parityBlock_queryFree)
    (branchPop_queryFree _ _ _ _ skip_queryFree skip_queryFree (Negation.negateOn_queryFree _)))

end HiddenCircuits.Complexity.DeterminantRuntime.Sign
