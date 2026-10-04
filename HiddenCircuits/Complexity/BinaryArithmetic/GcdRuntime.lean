import HiddenCircuits.Complexity.BinaryArithmetic.GcdBounds
import HiddenCircuits.Complexity.BinaryArithmetic.SignedBits
import HiddenCircuits.Complexity.OracleMove

/-! A fixed query-free finite stack program for Euclidean gcd. The loop tests the
actual current divisor and each body executes binary long division. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic.Gcd
open OracleBlock Polynomial

abbrev state (m n : ℕ) : Store 8 :=
  divStore (Computability.encodeNat m) (Computability.encodeNat n) [] [] [] [] [] [] []

noncomputable def step : OracleBlock 8 :=
  seq divisionBlock (seq (clear 3)
    (seq (moveOn 1 0 4 (by decide) (by decide) (by decide))
      (moveOn 2 1 4 (by decide) (by decide) (by decide))))
noncomputable def body (b : Bool) : OracleBlock 8 := seq (push 1 b) step
noncomputable def program : OracleBlock 8 := whilePop 1 (body false) (body true)

def divisionCost (m n : ℕ) : ℕ := 2*(Computability.encodeNat m).length+
  divLoopCost (Computability.encodeNat n) (Computability.encodeNat m).reverse [] []+3

def stepCost (m n : ℕ) : ℕ := divisionCost m n+(Computability.encodeNat (m/n)).length+
  6*(Computability.encodeNat n).length+6*(Computability.encodeNat (m%n)).length+17

theorem step_executes (g : BitString → ℕ) (m n : ℕ) (hn : 0<n) :
    step.Executes g (state m n) (state n (m%n)) (stepCost m n) := by
  have hdiv := divisionBlock_executes g (Computability.encodeNat m) (Computability.encodeNat n)
  rw [divFoldBits_encodeNat m n hn] at hdiv
  have hc : (clear (3:Fin 9)).Executes g
      (divStore [] (Computability.encodeNat n) (Computability.encodeNat (m%n))
        (Computability.encodeNat (m/n)) [] [] [] [] [])
      (divStore [] (Computability.encodeNat n) (Computability.encodeNat (m%n)) [] [] [] [] [] [])
      ((Computability.encodeNat (m/n)).length+1) := by
    convert clear_executes g (3:Fin 9) _ using 1
    funext i;fin_cases i <;> rfl
  have hm : (moveOn (1:Fin 9) 0 4 (by decide) (by decide) (by decide)).Executes g
      (divStore [] (Computability.encodeNat n) (Computability.encodeNat (m%n)) [] [] [] [] [] [])
      (divStore (Computability.encodeNat n) [] (Computability.encodeNat (m%n)) [] [] [] [] [] [])
      (6*(Computability.encodeNat n).length+5) := by
    convert moveOn_executes g (1:Fin 9) 0 4 (by decide) (by decide) (by decide)
      (divStore [] (Computability.encodeNat n) (Computability.encodeNat (m%n)) [] [] [] [] [] []) rfl using 1
    funext i;fin_cases i <;> simp [divStore]
  have hr : (moveOn (2:Fin 9) 1 4 (by decide) (by decide) (by decide)).Executes g
      (divStore (Computability.encodeNat n) [] (Computability.encodeNat (m%n)) [] [] [] [] [] [])
      (state n (m%n)) (6*(Computability.encodeNat (m%n)).length+5) := by
    convert moveOn_executes g (2:Fin 9) 1 4 (by decide) (by decide) (by decide)
      (divStore (Computability.encodeNat n) [] (Computability.encodeNat (m%n)) [] [] [] [] [] []) rfl using 1
    funext i;fin_cases i <;> simp [divStore]
  convert seq_executes _ _ g hdiv (seq_executes _ _ g hc (seq_executes _ _ g hm hr)) using 1 <;>
    simp only [stepCost,divisionCost] <;> omega

theorem stepCost_le (m n L : ℕ) (hn : 0<n)
    (hmL : (Computability.encodeNat m).length≤L) (hnL : (Computability.encodeNat n).length≤L) :
    stepCost m n+5≤100*(L+1)^2 := by
  have hd := divLoopCost_le (Computability.encodeNat n) (Computability.encodeNat m).reverse [] []
    (canonical_encodeNat n) canonical_nil canonical_nil (by simpa using hn)
  simp only [List.length_reverse] at hd
  have hq:=bits_length_mono (m/n) m (Nat.div_le_self _ _)
  have hr:=bits_length_mono (m%n) n (Nat.mod_lt _ hn).le
  unfold stepCost divisionCost
  nlinarith [Nat.mul_le_mul hmL hnL]

def cost (m n : ℕ) : ℕ := if h : n=0 then 1 else stepCost m n+5+cost n (m%n)
termination_by n
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

@[simp] theorem cost_zero (m : ℕ) : cost m 0=1 := by rw [cost];simp
lemma cost_succ (m n : ℕ) (hn : n≠0) : cost m n=stepCost m n+5+cost n (m%n) := by
  rw [cost];simp [hn]

lemma gcd_step (m n : ℕ) : Nat.gcd n (m%n)=Nat.gcd m n := by
  rw [Nat.gcd_comm n (m%n),←Nat.gcd_rec n m,Nat.gcd_comm]

theorem loop_executes (g : BitString → ℕ) (m n : ℕ) :
    WhileExecution 1 (body false) (body true) g (state m n) (state (Nat.gcd m n) 0) (cost m n) := by
  induction n using Nat.strong_induction_on generalizing m with
  | h n ih =>
    by_cases hn : n=0
    · subst n
      simp only [Nat.gcd_zero_right,cost_zero]
      exact WhileExecution.empty _ rfl
    · have ht:=ih (m%n) (Nat.mod_lt _ (Nat.pos_of_ne_zero hn)) n
      rw [gcd_step] at ht
      have he : Computability.encodeNat n≠[] := by simpa [encodeNat_eq_nil_iff] using hn
      cases hb : Computability.encodeNat n with
      | nil => exact False.elim (he hb)
      | cons b bs =>
        have hp : Function.update (state m n) (1:Fin 9) (b::bs)=state m n := by
          rw [←hb];exact Function.update_eq_self _ _
        have hbody : (body b).Executes g (Function.update (state m n) 1 bs)
            (state n (m%n)) (stepCost m n+3) := by
          have hpush:=push_executes g (1:Fin 9) b (Function.update (state m n) 1 bs)
          simp only [Function.update_self,Function.update_idem,hp] at hpush
          convert seq_executes _ _ g hpush (step_executes g m n (Nat.pos_of_ne_zero hn)) using 1 <;> omega
        rw [cost_succ m n hn]
        cases b
        · convert WhileExecution.zero (show state m n 1=false::bs from hb) hbody ht using 1 <;> omega
        · convert WhileExecution.one (show state m n 1=true::bs from hb) hbody ht using 1 <;> omega

theorem program_executes (g : BitString → ℕ) (m n : ℕ) :
    program.Executes g (state m n) (state (Nat.gcd m n) 0) (cost m n) :=
  whilePop_executes _ _ _ g (loop_executes g m n)

lemma cost_steps (m n L : ℕ) (hm : (Computability.encodeNat m).length≤L)
    (hn : (Computability.encodeNat n).length≤L) : cost m n≤steps m n*(100*(L+1)^2)+1 := by
  induction n using Nat.strong_induction_on generalizing m with
  | h n ih =>
    by_cases hz : n=0
    · subst n;simp
    · rw [cost_succ m n hz,steps_succ m n hz]
      have hr:=bits_length_mono (m%n) n (Nat.mod_lt _ (Nat.pos_of_ne_zero hz)).le
      have ht:=ih (m%n) (Nat.mod_lt _ (Nat.pos_of_ne_zero hz)) n hn (hr.trans hn)
      have hs:=stepCost_le m n L (Nat.pos_of_ne_zero hz) hm hn
      nlinarith

noncomputable def time : Polynomial ℕ := 200*(X+1)^3+1

theorem cost_polynomial (m n : ℕ) :
    cost m n≤time.eval ((Computability.encodeNat m).length+(Computability.encodeNat n).length) := by
  let L := (Computability.encodeNat m).length+(Computability.encodeNat n).length
  have hc:=cost_steps m n L (by dsimp [L];omega) (by dsimp [L];omega)
  have hs:=steps_length m n
  have hsL : steps m n≤2*L := by dsimp [L];omega
  have hh:=Nat.mul_le_mul_right (100*(L+1)^2) hsL
  simp only [time,eval_add,eval_mul,eval_ofNat,eval_pow,eval_X,eval_one]
  change cost m n≤200*(L+1)^3+1
  nlinarith [sq_nonneg (L:ℤ)]

lemma step_queryFree : step.QueryFree :=
  seq_queryFree _ _ divisionBlock_queryFree (seq_queryFree _ _ (clear_queryFree _)
    (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _) (moveOn_queryFree _ _ _ _ _ _)))
lemma body_queryFree (b : Bool) : (body b).QueryFree :=
  seq_queryFree _ _ (push_queryFree _ _) step_queryFree
lemma program_queryFree : program.QueryFree :=
  whilePop_queryFree _ _ _ (body_queryFree false) (body_queryFree true)

/-- Framed clean binary interface: no divisibility or execution certificate is an input. -/
theorem binary_executes (g : BitString → ℕ) (m n : ℕ) :
    ∃t,program.Executes g (binaryStore (Computability.encodeNat m) (Computability.encodeNat n))
      (binaryStore (Computability.encodeNat (Nat.gcd m n)) []) t ∧
      t≤time.eval ((Computability.encodeNat m).length+(Computability.encodeNat n).length) := by
  refine ⟨cost m n,?_,cost_polynomial m n⟩
  convert program_executes g m n using 1 <;> funext i <;> fin_cases i <;> rfl

end HiddenCircuits.Complexity.BinaryArithmetic.Gcd
