import HiddenCircuits.Complexity.DeterminantRuntime.Round
import HiddenCircuits.DH.Runtime.UnaryFor

/-! The actual n-round unary-controlled integer determinant computation. -/
namespace HiddenCircuits.Complexity.DeterminantRuntime
open OracleBlock BinaryArithmetic

noncomputable def loopProgram : OracleBlock 30 := DH.Runtime.UnaryFor.program 5 4 Round.program

theorem loop_executes (g : BitString → ℕ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    ∃ t, loopProgram.Executes g
      (Round.store n (encodeBitList (matrixWords A))
        (encodeBitList (matrixWords (1 : Matrix (Fin n) (Fin n) ℤ))) (signedBits 1) 0 n)
      (Round.store n (encodeBitList (matrixWords A))
        (encodeBitList (matrixWords (faddeevState A n).1)) (signedBits (faddeevState A n).2) n 0) t ∧
      t ≤ n*(Round.timePolynomial.eval (roundSizeBound A)+5)+1 := by
  let S := fun (i m : ℕ) (d : Matrix (Fin n) (Fin n) ℤ × ℤ) =>
    Round.store n (encodeBitList (matrixWords A)) (encodeBitList (matrixWords d.1)) (signedBits d.2) i m
  let Inv := fun (i : ℕ) (d : Matrix (Fin n) (Fin n) ℤ × ℤ) => d = faddeevState A i
  have hclock : ∀ i m d, S i m d (5 : Fin 31) = List.replicate m true := by intros;rfl
  have hpop : ∀ i m d, Function.update (S i (m+1) d) (5 : Fin 31) (List.replicate m true) = S i m d := by
    intro i m d; funext q; fin_cases q <;> rfl
  have hinc : ∀ i m d, Function.update (S i m d) (4 : Fin 31) (true::S i m d 4) = S (i+1) m d := by
    intro i m d; funext q; fin_cases q <;> rfl
  have hbody : ∀ i m d, Inv i d → i<n → ∃ t, Round.program.Executes g (S i m d)
      (S i m (faddeevStep A i d)) t ∧ t ≤ Round.timePolynomial.eval (roundSizeBound A) ∧
      Inv (i+1) (faddeevStep A i d) := by
    intro i m d hd hi
    change d = faddeevState A i at hd
    subst d
    obtain ⟨t,ht,hb⟩ := Round.prefix_executes g A i m hi
    exact ⟨t,ht,hb,rfl⟩
  obtain ⟨t,ht,hb,hfinal⟩ := DH.Runtime.UnaryFor.executes (5 : Fin 31) 4 Round.program g
    (faddeevStep A) S Inv (Round.timePolynomial.eval (roundSizeBound A)) n hclock hpop hinc hbody
    0 n (1,1) rfl (by omega)
  change DH.Runtime.UnaryFor.iterate (faddeevStep A) 0 n (1,1) = faddeevState A (0+n) at hfinal
  rw [hfinal] at ht
  exact ⟨t,by simpa only [Nat.zero_add,S] using ht,hb⟩

theorem loopProgram_queryFree : loopProgram.QueryFree :=
  DH.Runtime.UnaryFor.queryFree _ _ _ Round.queryFree

end HiddenCircuits.Complexity.DeterminantRuntime
