import HiddenCircuits.Approximation.SamplerRuntime.CoreParts

/-! A complete finite sampler core from canonical endpoints alone, including
empty-instance behavior and a closed polynomial operational time bound. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.Core
open Complexity Complexity.OracleBlock GraphReduction.MonotoneEndpointEncoding Polynomial

variable {n : ℕ}

def evaluate (E : MonotoneEndpoints n) (N : ℕ) (tape : BitString) : BitString :=
  match E.startingPermutation with
  | none => []
  | some π => Output.success (Iteration.iterate E (Budget.steps N) π tape).val

noncomputable def timePolynomial : Polynomial ℕ :=
  20000000*(X+1)^6 + UnaryPolynomial.polynomialTime Budget.stepsPolynomial+
    Budget.stepsPolynomial*(20000000*(X+1)^4+2)+40*(X+1)^2+100

lemma initialization_bound (E : MonotoneEndpoints n) (N : ℕ) (hn : n≤N) :
    2000*((encodeBitList (rows E.lo)).length+(encodeBitList (rows E.hi)).length+n+1)^3≤20000000*(N+1)^6 := by
  have hl := Switch.rows_encoded_length E.lo (fun i => (E.lo_le_hi i).trans (E.hi_le i))
  have hh := Switch.rows_encoded_length E.hi E.hi_le
  have hn2 := Nat.pow_le_pow_left hn 2
  have hbase : (encodeBitList (rows E.lo)).length+(encodeBitList (rows E.hi)).length+n+1≤10*(N+1)^2 := by nlinarith
  have hp := Nat.mul_le_mul_left 2000 (Nat.pow_le_pow_left hbase 3)
  have he : (10*(N+1)^2)^3=1000*(N+1)^6 := by ring
  rw [he] at hp
  omega

lemma branch_pop (ls hs : BitString) (n N : ℕ) (tape out : BitString) (flag : Bool) :
    Function.update (state ls hs n N tape out [] [] [flag]) 26 []=state ls hs n N tape out [] [] [] := by
  funext r;fin_cases r <;> rfl

/-- Endpoint-only initialization, actual fair-bit steps and exact failure on
empty instances are assembled into one fixed twenty-seven-stack program. -/
theorem program_executes (g : BitString → ℕ) (E : MonotoneEndpoints n) (N : ℕ) (hn : n≤N) (tape : BitString) :
    ∃s : Store 26,∃t,program.Executes g
      (state (encodeBitList (rows E.lo)) (encodeBitList (rows E.hi)) n N tape [] [] [] []) s t ∧
      s 2=evaluate E N tape ∧ t≤timePolynomial.eval N := by
  let ls := encodeBitList (rows E.lo)
  let hs := encodeBitList (rows E.hi)
  obtain ⟨a,ha,hba⟩ := initialize_executes g (rows E.lo) (rows E.hi) n N tape
  have hba' : a≤20000000*(N+1)^6 := hba.trans (initialization_bound E N hn)
  by_cases h : E.Admissible (Equiv.refl (Fin n))
  · let π : E.Permutations := ⟨Equiv.refl _,h⟩
    have hflag : Diagonal.check (rows E.lo) (rows E.hi) 0 n=true := (Initialize.flag_nonempty E).mpr ⟨π⟩
    have hident : Identity.evaluate (unary n)=Output.witness π.val := by
      rw [Identity.evaluate_unary]
      rfl
    rw [hflag,hident] at ha
    obtain ⟨b,hb,hbb⟩ := success_executes g E N π tape
    have hbranch := branchPop_true (26:Fin 27) (clear 2) (clear 2) success g
      (s:=state ls hs n N tape (Output.witness π.val) [] [] [true]) rfl
      (by rw [branch_pop];exact hb)
    refine ⟨_,a+(b+2)+2,seq_executes _ _ g ha hbranch,?_,?_⟩
    · change Output.success (Iteration.iterate E (Budget.steps N) π tape).val=evaluate E N tape
      simp [evaluate,MonotoneEndpoints.startingPermutation,h,π]
    · have hm4 := Nat.pow_le_pow_left (show n+1≤N+1 by omega) 4
      have hm2 := Nat.pow_le_pow_left (show n+1≤N+1 by omega) 2
      have hmul := Nat.mul_le_mul_left (Budget.steps N) (show 20000000*(n+1)^4+2≤20000000*(N+1)^4+2 by omega)
      simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
        Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one,Budget.steps_eval]
      change _≤20000000*(N+1)^6+(UnaryPolynomial.polynomialTime Budget.stepsPolynomial).eval N+
        Budget.steps N*(20000000*(N+1)^4+2)+40*(N+1)^2+100
      omega
  · have hflag : Diagonal.check (rows E.lo) (rows E.hi) 0 n=false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      exact h (Initialize.identity_admissible E ht)
    rw [hflag] at ha
    have hb : (clear (2:Fin 27)).Executes g
        (state ls hs n N tape (Identity.evaluate (unary n)) [] [] [])
        (state ls hs n N tape [] [] [] []) ((Identity.evaluate (unary n)).length+1) := by
      convert clear_executes g (2:Fin 27) (state ls hs n N tape (Identity.evaluate (unary n)) [] [] []) using 1
      funext r;fin_cases r <;> rfl
    have hbranch := branchPop_false (26:Fin 27) (clear 2) (clear 2) success g
      (s:=state ls hs n N tape (Identity.evaluate (unary n)) [] [] [false]) rfl
      (by rw [branch_pop];exact hb)
    refine ⟨_,a+((Identity.evaluate (unary n)).length+1+2)+2,seq_executes _ _ g ha hbranch,?_,?_⟩
    · change ([]:BitString)=evaluate E N tape
      simp [evaluate,MonotoneEndpoints.startingPermutation,h]
    · have hlen : (Identity.evaluate (unary n)).length=n*(n+1) := by
        simp only [Identity.evaluate,List.length_replicate,Identity.words_encode_length,Nat.mul_zero,Nat.zero_mul,Nat.zero_add]
      rw [hlen]
      simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
        Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one,Budget.steps_eval]
      have hn2 := Nat.pow_le_pow_left (show n+1≤N+1 by omega) 2
      nlinarith

end HiddenCircuits.Approximation.SamplerRuntime.Core
