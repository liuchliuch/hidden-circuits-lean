import HiddenCircuits.Complexity.BinaryArithmetic.CleanOperations
import HiddenCircuits.Complexity.GridTermAlgebra

/-! Actual final exact integer division and removal of the canonical positive
sign. The counting output is the ordinary binary natural encoding. -/
namespace HiddenCircuits.Complexity.FinalCountRuntime
open OracleBlock BinaryArithmetic

def dropSign : OracleBlock 8 where
  labelCount := 2
  start := 0
  exit := 1
  code q := if q=0 then .pop 0 1 1 1 else .halt
  exit_halt := rfl

lemma dropSign_executes (g : BitString → ℕ) (z : ℕ) :
    dropSign.Executes g (binaryStore (signedBits (z : ℤ)) [])
      (binaryStore (Computability.encodeNat z) []) 1 := by
  have hs : signedBits (z : ℤ)=false::Computability.encodeNat z := by
    simp [signedBits,negative]
  rw [hs]
  apply OracleMachine.Steps.single
  change some (dropSign.config dropSign.exit (Function.update
      (binaryStore (false::Computability.encodeNat z) []) 0 (Computability.encodeNat z)),1) =
    some (dropSign.config dropSign.exit (binaryStore (Computability.encodeNat z) []),1)
  apply congrArg (fun s : Store 8 => some (dropSign.config dropSign.exit s,1))
  funext i;fin_cases i <;> rfl

noncomputable def program : OracleBlock 8 := seq cleanDivide dropSign
noncomputable def time : Polynomial ℕ := cleanDivideTime+3

theorem program_executes (g : BitString → ℕ) (a b : ℤ) (z : ℕ) (hb : b≠0) (ha : a=(z : ℤ)*b) :
    ∃ c, program.Executes g (binaryStore (signedBits a) (signedBits b))
      (binaryStore (Computability.encodeNat z) []) c ∧
      c≤time.eval ((signedBits a).length+(signedBits b).length) := by
  have hd : b∣a := ⟨z,by rw [ha];ring⟩
  have hq : a/b=(z : ℤ) := by rw [ha];exact Int.mul_ediv_cancel _ hb
  obtain ⟨c,hc,hbound⟩ := cleanDivide_executes g a b hb hd
  rw [hq] at hc
  refine ⟨c+1+2,seq_executes _ _ g hc (dropSign_executes g z),?_⟩
  simp only [time,Polynomial.eval_add,Polynomial.eval_ofNat]
  omega

/-- The real source grid's exact numerator/denominator identity discharges both
arithmetic preconditions and yields the actual natural counting answer. -/
theorem source_executes (g : BitString → ℕ) {n m : ℕ} (F : CNF n m) :
    ∃ c, program.Executes g
      (binaryStore (signedBits (gridNumerator n m (fun i j => (F.cloneCount i.val j.val : ℤ))))
        (signedBits (gridDenominator n m)))
      (binaryStore (Computability.encodeNat F.satCount) []) c ∧
      c≤time.eval ((signedBits (gridNumerator n m (fun i j => (F.cloneCount i.val j.val : ℤ)))).length+
        (signedBits (gridDenominator n m)).length) :=
  program_executes g _ _ F.satCount (gridDenominator_ne_zero n m) F.gridNumerator_exact

lemma dropSign_queryFree : dropSign.QueryFree := by
  intro q i o next;fin_cases q <;> simp [dropSign,machine]
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ cleanDivide_queryFree dropSign_queryFree

end HiddenCircuits.Complexity.FinalCountRuntime
