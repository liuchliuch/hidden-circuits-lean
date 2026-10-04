import HiddenCircuits.Complexity.BinaryArithmetic.Multiplication
import HiddenCircuits.Complexity.BinaryArithmetic.DivisionBits
import Mathlib.Data.Nat.Factorial.Basic

/-! A unary-clock factorial program built from actual increment/multiplication bit blocks. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic
open OracleBlock OracleMachine

def factorialStore (a k p t u v clock : BitString) : Store 6 := fun i =>
  if i.val=0 then a else if i.val=1 then k else if i.val=2 then p else
    if i.val=3 then t else if i.val=4 then u else if i.val=5 then v else clock

def factorialIncEmbedding : Fin 2 ↪ Fin 7 where
  toFun i := if i=0 then 1 else 3
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

def factorialMulEmbedding : Fin 6 ↪ Fin 7 where
  toFun i := i.castLE (by decide)
  inj' := by intro i j h;exact Fin.ext (congrArg (fun q : Fin 7 => q.val) h)

noncomputable def factorialInc : OracleBlock 6 := rename incrementBlock factorialIncEmbedding
noncomputable def factorialMul : OracleBlock 6 := rename multiplicationBlock factorialMulEmbedding
noncomputable def factorialRestore : OracleBlock 6 := seq (reverseOn 2 3 (by decide)) (reverseOn 3 0 (by decide))
noncomputable def factorialBody : OracleBlock 6 := seq factorialInc (seq factorialMul factorialRestore)

 theorem factorialInc_executes (g : BitString → ℕ) (a k clock : BitString) :
    factorialInc.Executes g (factorialStore a k [] [] [] [] clock)
      (factorialStore a (BitPrograms.incrementBits k) [] [] [] [] clock)
      (4*BitPrograms.leadingOnes k+3) := by
  apply rename_executes_to incrementBlock factorialIncEmbedding g (incrementBlock_executes g k)
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | (exfalso;exact hi 0 rfl) | (exfalso;exact hi 1 rfl)

 theorem factorialMul_executes (g : BitString → ℕ) (a k clock : BitString) :
    factorialMul.Executes g (factorialStore a k [] [] [] [] clock)
      (factorialStore [] k (mulBits a k) [] [] [] clock)
      (2*a.length+mulLoopCost k a.reverse []+3) := by
  apply rename_executes_to multiplicationBlock factorialMulEmbedding g (multiplicationBlock_executes g a k)
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | (exfalso;exact hi 0 rfl) | (exfalso;exact hi 1 rfl) | (exfalso;exact hi 2 rfl)

 theorem factorialRestore_executes (g : BitString → ℕ) (p k clock : BitString) :
    factorialRestore.Executes g (factorialStore [] k p [] [] [] clock)
      (factorialStore p k [] [] [] [] clock) (4*p.length+4) := by
  have h1 : (reverseOn (2:Fin 7) 3 (by decide)).Executes g (factorialStore [] k p [] [] [] clock)
      (factorialStore [] k [] p.reverse [] [] clock) (2*p.length+1) := by
    convert reverseOn_executes g (2:Fin 7) 3 (by decide) (factorialStore [] k p [] [] [] clock) using 1
    funext i;fin_cases i <;> simp [factorialStore]
  have h2 : (reverseOn (3:Fin 7) 0 (by decide)).Executes g (factorialStore [] k [] p.reverse [] [] clock)
      (factorialStore p k [] [] [] [] clock) (2*p.length+1) := by
    convert reverseOn_executes g (3:Fin 7) 0 (by decide) (factorialStore [] k [] p.reverse [] [] clock) using 1
    · funext i;fin_cases i <;> simp [factorialStore]
    · simp [factorialStore]
  convert seq_executes _ _ g h1 h2 using 1 <;> omega

def factorialBodyCost (a k : BitString) : ℕ :=
  4*BitPrograms.leadingOnes k+3+
    (2*a.length+mulLoopCost (BitPrograms.incrementBits k) a.reverse []+3+
      (4*(mulBits a (BitPrograms.incrementBits k)).length+4)+2)+2

 theorem factorialBody_executes (g : BitString → ℕ) (a k clock : BitString) :
    factorialBody.Executes g (factorialStore a k [] [] [] [] clock)
      (factorialStore (mulBits a (BitPrograms.incrementBits k)) (BitPrograms.incrementBits k) [] [] [] [] clock)
      (factorialBodyCost a k) :=
  seq_executes _ _ g (factorialInc_executes g a k clock)
    (seq_executes _ _ g (factorialMul_executes g a (BitPrograms.incrementBits k) clock)
      (factorialRestore_executes g (mulBits a (BitPrograms.incrementBits k)) (BitPrograms.incrementBits k) clock))

 theorem factorialBody_nat (g : BitString → ℕ) (k : ℕ) (clock : BitString) :
    factorialBody.Executes g (factorialStore (Computability.encodeNat k.factorial) (Computability.encodeNat k) [] [] [] [] clock)
      (factorialStore (Computability.encodeNat (k+1).factorial) (Computability.encodeNat (k+1)) [] [] [] [] clock)
      (factorialBodyCost (Computability.encodeNat k.factorial) (Computability.encodeNat k)) := by
  simpa [Nat.factorial_succ,Nat.mul_comm] using
    factorialBody_executes g (Computability.encodeNat k.factorial) (Computability.encodeNat k) clock

 theorem factorial_binary_length (k : ℕ) : (Computability.encodeNat k.factorial).length≤k*k+1 := by
  rw [encodeNat_length]
  have hk : k≤2^k := (Nat.lt_two_pow_self (n := k)).le
  have hh : k.factorial≤2^(k*k) :=
    (Nat.factorial_le_pow k).trans ((Nat.pow_le_pow_left hk k).trans_eq (pow_mul 2 k k).symm)
  have hs := Nat.size_le_size hh
  rwa [Nat.size_pow] at hs


/-- A common bound for all binary words used before step `n+1`. -/
def factorialWordBound (n : ℕ) : ℕ := (n+1)*(n+1)+1

def factorialBodyBound (n : ℕ) : ℕ :=
  let L := factorialWordBound n
  L*(5*(L*(L+2))+10*L+22)+10*L+15

 theorem factorialBodyCost_le (k n : ℕ) (hk : k ≤ n) :
    factorialBodyCost (Computability.encodeNat k.factorial) (Computability.encodeNat k) ≤
      factorialBodyBound n := by
  have hn : k+1 ≤ factorialWordBound n := by unfold factorialWordBound; nlinarith
  have hkl : (Computability.encodeNat k).length ≤ factorialWordBound n := by
    rw [encodeNat_length]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := k))).trans (by omega)
  have hin : (Computability.encodeNat (k+1)).length ≤ factorialWordBound n := by
    rw [encodeNat_length]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := k+1))).trans hn
  have ha : (Computability.encodeNat k.factorial).length ≤ factorialWordBound n :=
    (factorial_binary_length k).trans (by unfold factorialWordBound; nlinarith)
  have hp : (Computability.encodeNat (k+1).factorial).length ≤ factorialWordBound n :=
    (factorial_binary_length (k+1)).trans (by unfold factorialWordBound; nlinarith)
  have ho := (BitPrograms.leadingOnes_le_length (Computability.encodeNat k)).trans hkl
  have hm := mulLoopCost_le (Computability.encodeNat (k+1))
    (Computability.encodeNat k.factorial).reverse []
  simp only [List.length_reverse,List.length_nil,Nat.zero_add] at hm
  have hm' : mulLoopCost (Computability.encodeNat (k+1))
      (Computability.encodeNat k.factorial).reverse [] ≤
      1+factorialWordBound n*(5*(factorialWordBound n*(factorialWordBound n+2))+
        10*factorialWordBound n+22) := hm.trans (by gcongr)
  unfold factorialBodyCost factorialBodyBound
  simp only [BitPrograms.increment_encodeNat,mulBits_encodeNat,
    ← Nat.factorial_succ,Nat.mul_comm k.factorial (k+1)]
  omega

noncomputable def factorialLoop : OracleBlock 6 := whilePop 6 factorialBody factorialBody

def factorialLoopCost (k : ℕ) : ℕ → ℕ
  | 0 => 1
  | r+1 => 1+factorialBodyCost (Computability.encodeNat k.factorial)
      (Computability.encodeNat k)+1+factorialLoopCost (k+1) r

 theorem factorialLoop_executes (g : BitString → ℕ) (clock : BitString) (k : ℕ) :
    factorialLoop.Executes g
      (factorialStore (Computability.encodeNat k.factorial) (Computability.encodeNat k) [] [] [] [] clock)
      (factorialStore (Computability.encodeNat (k+clock.length).factorial)
        (Computability.encodeNat (k+clock.length)) [] [] [] [] [])
      (factorialLoopCost k clock.length) := by
  apply whilePop_executes
  induction clock generalizing k with
  | nil =>
    simpa [factorialLoopCost] using (WhileExecution.empty
      (factorialStore (Computability.encodeNat k.factorial) (Computability.encodeNat k) [] [] [] [] []) rfl)
  | cons bit rest ih =>
    have hs : Function.update
        (factorialStore (Computability.encodeNat k.factorial) (Computability.encodeNat k) [] [] [] [] (bit::rest)) 6 rest =
        factorialStore (Computability.encodeNat k.factorial) (Computability.encodeNat k) [] [] [] [] rest := by
      funext i; fin_cases i <;> rfl
    have hb := factorialBody_nat g k rest
    rw [← hs] at hb
    cases bit
    · have h := WhileExecution.zero rfl hb (ih (k+1))
      simpa only [List.length_cons,factorialLoopCost,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
    · have h := WhileExecution.one rfl hb (ih (k+1))
      simpa only [List.length_cons,factorialLoopCost,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

 theorem factorialLoopCost_le (r k n : ℕ) (h : k+r ≤ n) :
    factorialLoopCost k r ≤ 1+r*(factorialBodyBound n+2) := by
  induction r generalizing k with
  | zero => simp [factorialLoopCost]
  | succ r ih =>
    have ht := ih (k+1) (by omega)
    have hb := factorialBodyCost_le k n (by omega)
    simp only [factorialLoopCost]
    nlinarith

noncomputable def factorialInit : OracleBlock 6 :=
  seq (reverseOn 0 6 (by decide)) (push 0 true)

/-- A fixed seven-stack program: consume a unary input, compute factorial by
actual binary increments and multiplications, and erase the binary counter. -/
noncomputable def factorialBlock : OracleBlock 6 :=
  seq factorialInit (seq factorialLoop (clear 1))

 theorem factorialInit_executes (g : BitString → ℕ) (clock : BitString) :
    factorialInit.Executes g (factorialStore clock [] [] [] [] [] [])
      (factorialStore [true] [] [] [] [] [] clock.reverse) (2*clock.length+4) := by
  have hr : (reverseOn (0 : Fin 7) 6 (by decide)).Executes g
      (factorialStore clock [] [] [] [] [] [])
      (factorialStore [] [] [] [] [] [] clock.reverse) (2*clock.length+1) := by
    convert reverseOn_executes g (0 : Fin 7) 6 (by decide)
      (factorialStore clock [] [] [] [] [] []) using 1
    funext i; fin_cases i <;> simp [factorialStore]
  have hp : (push (0 : Fin 7) true).Executes g
      (factorialStore [] [] [] [] [] [] clock.reverse)
      (factorialStore [true] [] [] [] [] [] clock.reverse) 1 := by
    convert push_executes g (0 : Fin 7) true (factorialStore [] [] [] [] [] [] clock.reverse) using 1
    funext i; fin_cases i <;> rfl
  convert seq_executes _ _ g hr hp using 1 <;> omega

 theorem factorialBlock_executes (g : BitString → ℕ) (clock : BitString) :
    factorialBlock.Executes g (factorialStore clock [] [] [] [] [] [])
      (factorialStore (Computability.encodeNat clock.length.factorial) [] [] [] [] [] [])
      (2*clock.length+factorialLoopCost 0 clock.length+
        (Computability.encodeNat clock.length).length+9) := by
  have hi := factorialInit_executes g clock
  have hl := factorialLoop_executes g clock.reverse 0
  simp only [List.length_reverse,Nat.zero_add,Nat.factorial_zero] at hl
  have hc : (clear (1 : Fin 7)).Executes g
      (factorialStore (Computability.encodeNat clock.length.factorial) (Computability.encodeNat clock.length) [] [] [] [] [])
      (factorialStore (Computability.encodeNat clock.length.factorial) [] [] [] [] [] [])
      ((Computability.encodeNat clock.length).length+1) := by
    convert clear_executes g (1 : Fin 7)
      (factorialStore (Computability.encodeNat clock.length.factorial) (Computability.encodeNat clock.length) [] [] [] [] []) using 1
    funext i; fin_cases i <;> rfl
  convert seq_executes _ _ g hi (seq_executes _ _ g hl hc) using 1 <;> omega

noncomputable def factorialTime : Polynomial ℕ :=
  let L : Polynomial ℕ := (Polynomial.X+1)^2+1
  Polynomial.X*(L*(5*(L*(L+2))+10*L+22)+10*L+17)+3*Polynomial.X+10

 theorem factorial_polynomial (g : BitString → ℕ) (clock : BitString) :
    ∃ t, factorialBlock.Executes g (factorialStore clock [] [] [] [] [] [])
      (factorialStore (Computability.encodeNat clock.length.factorial) [] [] [] [] [] []) t ∧
      t ≤ factorialTime.eval clock.length := by
  refine ⟨_,factorialBlock_executes g clock,?_⟩
  have hl := factorialLoopCost_le clock.length 0 clock.length (by omega)
  have hs : (Computability.encodeNat clock.length).length ≤ clock.length := by
    rw [encodeNat_length]; exact Nat.size_le.mpr Nat.lt_two_pow_self
  simp only [factorialTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_ofNat,Polynomial.eval_one,Polynomial.eval_X]
  unfold factorialBodyBound factorialWordBound at hl
  simp only [pow_two]
  nlinarith

 theorem factorial_unary (g : BitString → ℕ) (n : ℕ) :
    ∃ t, factorialBlock.Executes g (factorialStore (List.replicate n true) [] [] [] [] [] [])
      (factorialStore (Computability.encodeNat n.factorial) [] [] [] [] [] []) t ∧
      t ≤ factorialTime.eval n := by
  simpa only [List.length_replicate] using factorial_polynomial g (List.replicate n true)

lemma factorialIncrement_queryFree : incrementBlock.QueryFree := by
  intro q i o next
  fin_cases q <;> simp [machine,incrementBlock,BitPrograms.incrementMachine]

lemma factorialBody_queryFree : factorialBody.QueryFree :=
  seq_queryFree _ _ (rename_queryFree _ _ factorialIncrement_queryFree)
    (seq_queryFree _ _ (rename_queryFree _ _ multiplicationBlock_queryFree)
      (seq_queryFree _ _ (reverseOn_queryFree _ _ _) (reverseOn_queryFree _ _ _)))

lemma factorialBlock_queryFree : factorialBlock.QueryFree :=
  seq_queryFree _ _ (seq_queryFree _ _ (reverseOn_queryFree _ _ _) (push_queryFree _ _))
    (seq_queryFree _ _ (whilePop_queryFree _ _ _ factorialBody_queryFree factorialBody_queryFree)
      (clear_queryFree _))

 theorem factorial_runs (g : BitString → ℕ) (n : ℕ) :
    ∃ (c : factorialBlock.machine.Config) (t : ℕ),
      factorialBlock.machine.Runs g
        (factorialBlock.config factorialBlock.start
          (factorialStore (List.replicate n true) [] [] [] [] [] [])) c t ∧
      c.stack = factorialStore (Computability.encodeNat n.factorial) [] [] [] [] [] [] ∧
      t ≤ factorialTime.eval n := by
  obtain ⟨t,ht,hbound⟩ := factorial_unary g n
  refine ⟨factorialBlock.config factorialBlock.exit
    (factorialStore (Computability.encodeNat n.factorial) [] [] [] [] [] []),t,?_,rfl,hbound⟩
  apply (runs_iff_steps_halt _).mpr
  refine ⟨ht,?_⟩
  simp [OracleMachine.step,machine,config,factorialBlock.exit_halt]

end HiddenCircuits.Complexity.BinaryArithmetic
