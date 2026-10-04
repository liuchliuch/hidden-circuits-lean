import HiddenCircuits.Complexity.OracleLibrary
import HiddenCircuits.Complexity.OracleBlockNoQuery
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Unary quotient and remainder by a real cyclic divisor clock. The positive
divisor is preserved; every dividend bit is consumed by the finite program. -/
namespace HiddenCircuits.Complexity.UnaryDivision
open OracleBlock OracleMachine

/-- Ports: dividend 0, preserved divisor 1, quotient 2, remainder 3,
remaining divisor clock 4, and copy scratch 5. -/
 def store (source : BitString) (d q r : ℕ) (clock : BitString) : Store 5 := fun i =>
  if i.val=0 then source else if i.val=1 then List.replicate d true
  else if i.val=2 then List.replicate q true else if i.val=3 then List.replicate r true
  else if i.val=4 then clock else []

 def stepQR (d q r : ℕ) : ℕ × ℕ := if r+1=d then (q+1,0) else (q,r+1)
 def foldQR (d : ℕ) : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0,q,r => (q,r)
  | n+1,q,r => foldQR d n (stepQR d q r).1 (stepQR d q r).2

 theorem stepQR_remainder (d q r : ℕ) (hd : 0<d) (hr : r<d) : (stepQR d q r).2<d := by
  unfold stepQR; split <;> simp only <;> omega

 theorem stepQR_equation (d q r : ℕ) :
    (stepQR d q r).1*d+(stepQR d q r).2=q*d+r+1 := by
  unfold stepQR; split
  · rename_i h; simp only; nlinarith
  · simp only; omega

 theorem foldQR_remainder (d n q r : ℕ) (hd : 0<d) (hr : r<d) : (foldQR d n q r).2<d := by
  induction n generalizing q r with
  | zero => exact hr
  | succ n ih => exact ih _ _ (stepQR_remainder d q r hd hr)

 theorem foldQR_equation (d n q r : ℕ) :
    (foldQR d n q r).1*d+(foldQR d n q r).2=q*d+r+n := by
  induction n generalizing q r with
  | zero => simp [foldQR]
  | succ n ih => simp only [foldQR,ih,stepQR_equation]; omega

 theorem foldQR_correct (m d : ℕ) (hd : 0<d) : foldQR d m 0 0=(m/d,m%d) := by
  have hr := foldQR_remainder d m 0 0 hd hd
  have he := foldQR_equation d m 0 0
  simp only [Nat.zero_mul,Nat.zero_add] at he
  apply Prod.ext
  · calc
      (foldQR d m 0 0).1 = ((foldQR d m 0 0).1*d+(foldQR d m 0 0).2)/d := by
        rw [Nat.add_comm,Nat.add_mul_div_right _ _ hd,Nat.div_eq_of_lt hr,Nat.zero_add]
      _ = m/d := congrArg (fun x => x/d) he
  · calc
      (foldQR d m 0 0).2 = ((foldQR d m 0 0).1*d+(foldQR d m 0 0).2)%d := by
        simp [Nat.add_mod,Nat.mod_eq_of_lt hr]
      _ = m%d := congrArg (fun x => x%d) he

 def dropClock : OracleBlock 5 where
  labelCount := 2
  start := 0
  exit := 1
  code q := if q=0 then .pop 4 1 1 1 else .halt
  exit_halt := rfl
 noncomputable def completeCycle : OracleBlock 5 :=
  seq (push 2 true) (seq (clear 3) (copyOn 1 4 5 (by decide) (by decide) (by decide)))
 noncomputable def testBoundary : OracleBlock 5 :=
  branchPop 4 completeCycle (push 4 false) (push 4 true)
 noncomputable def body : OracleBlock 5 := seq dropClock (seq (push 3 true) testBoundary)
 noncomputable def loop : OracleBlock 5 := whilePop 0 body body
 noncomputable def block : OracleBlock 5 :=
  seq (copyOn 1 4 5 (by decide) (by decide) (by decide)) (seq loop (clear 4))

 theorem dropClock_executes (g : BitString → ℕ) (source : BitString) (d q r k : ℕ) :
    dropClock.Executes g (store source d q r (List.replicate (k+1) true))
      (store source d q r (List.replicate k true)) 1 := by
  apply OracleMachine.Steps.single
  change some ((⟨(1 : Fin 2),Function.update (store source d q r (List.replicate (k+1) true)) (4 : Fin 6)
      (List.replicate k true)⟩ : dropClock.machine.Config),1) =
    some ((⟨(1 : Fin 2),store source d q r (List.replicate k true)⟩ : dropClock.machine.Config),1)
  apply congrArg (fun s : Store 5 => some ((⟨(1 : Fin 2),s⟩ : dropClock.machine.Config),1))
  funext i; fin_cases i <;> rfl

 theorem completeCycle_executes (g : BitString → ℕ) (source : BitString) (d q : ℕ) :
    completeCycle.Executes g (store source d q d [])
      (store source d (q+1) 0 (List.replicate d true)) (6*d+8) := by
  have h1 : (push (2 : Fin 6) true).Executes g (store source d q d []) (store source d (q+1) d []) 1 := by
    convert push_executes g (2 : Fin 6) true (store source d q d []) using 1
    funext i; fin_cases i <;> simp [store,List.replicate_succ]
  have h2 : (clear (3 : Fin 6)).Executes g (store source d (q+1) d []) (store source d (q+1) 0 []) (d+1) := by
    convert clear_executes g (3 : Fin 6) (store source d (q+1) d []) using 1
    · funext i; fin_cases i <;> rfl
    · simp [store]
  have h3 : (copyOn (1 : Fin 6) 4 5 (by decide) (by decide) (by decide)).Executes g
      (store source d (q+1) 0 []) (store source d (q+1) 0 (List.replicate d true)) (5*d+2) := by
    convert copyOn_executes g (1 : Fin 6) 4 5 (by decide) (by decide) (by decide)
      (store source d (q+1) 0 []) rfl using 1
    · funext i; fin_cases i <;> simp [store]
    · simp [store]
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 h3) using 1 <;> omega

 theorem testBoundary_nonempty (g : BitString → ℕ) (source : BitString) (d q r k : ℕ) :
    testBoundary.Executes g (store source d q r (List.replicate (k+1) true))
      (store source d q r (List.replicate (k+1) true)) 3 := by
  have hp : (push (4 : Fin 6) true).Executes g
      (Function.update (store source d q r (List.replicate (k+1) true)) (4 : Fin 6) (List.replicate k true))
      (store source d q r (List.replicate (k+1) true)) 1 := by
    convert push_executes g (4 : Fin 6) true
      (Function.update (store source d q r (List.replicate (k+1) true)) (4 : Fin 6) (List.replicate k true)) using 1
    funext i; fin_cases i <;> rfl
  exact branchPop_true _ _ _ _ g rfl hp

 theorem body_executes (g : BitString → ℕ) (source : BitString) (d q r : ℕ) (hd : 0<d) (hr : r<d) :
    ∃ t, body.Executes g (store source d q r (List.replicate (d-r) true))
      (store source d (stepQR d q r).1 (stepQR d q r).2 (List.replicate (d-(stepQR d q r).2) true)) t ∧
      t+2≤6*d+18 := by
  have hc : d-r=(d-r-1)+1 := by omega
  have h1 := dropClock_executes g source d q r (d-r-1)
  rw [← hc] at h1
  have h2 : (push (3 : Fin 6) true).Executes g
      (store source d q r (List.replicate (d-r-1) true))
      (store source d q (r+1) (List.replicate (d-r-1) true)) 1 := by
    convert push_executes g (3 : Fin 6) true (store source d q r (List.replicate (d-r-1) true)) using 1
    funext i; fin_cases i <;> simp [store,List.replicate_succ]
  by_cases h : r+1=d
  · have hzero : d-r-1=0 := by omega
    have h3 : testBoundary.Executes g (store source d q (r+1) (List.replicate (d-r-1) true))
        (store source d (q+1) 0 (List.replicate d true)) (6*d+10) := by
      rw [h,hzero,List.replicate_zero]
      exact branchPop_empty _ _ _ _ g rfl (completeCycle_executes g source d q)
    refine ⟨6*d+16,?_,by omega⟩
    convert (show body.Executes g _ _ _ from seq_executes _ _ g h1 (seq_executes _ _ g h2 h3)) using 1 <;> simp [stepQR,h] <;> omega
  · have hpos : d-r-1=(d-r-2)+1 := by omega
    have h3 := testBoundary_nonempty g source d q (r+1) (d-r-2)
    rw [← hpos] at h3
    refine ⟨9,?_,by omega⟩
    have he : d-r-1=d-(r+1) := by omega
    simpa [stepQR,h,he] using seq_executes _ _ g h1 (seq_executes _ _ g h2 h3)

 theorem loop_executes (g : BitString → ℕ) (m d q r : ℕ) (hd : 0<d) (hr : r<d) :
    ∃ t, loop.Executes g (store (List.replicate m true) d q r (List.replicate (d-r) true))
      (store [] d (foldQR d m q r).1 (foldQR d m q r).2 (List.replicate (d-(foldQR d m q r).2) true)) t ∧
      t≤m*(6*d+18)+1 := by
  suffices ∃ t, WhileExecution (0 : Fin 6) body body g
      (store (List.replicate m true) d q r (List.replicate (d-r) true))
      (store [] d (foldQR d m q r).1 (foldQR d m q r).2 (List.replicate (d-(foldQR d m q r).2) true)) t ∧
      t≤m*(6*d+18)+1 by
    obtain ⟨t,ht,hbound⟩ := this
    exact ⟨t,whilePop_executes _ _ _ g ht,hbound⟩
  induction m generalizing q r with
  | zero => exact ⟨1,WhileExecution.empty _ rfl,by simp⟩
  | succ m ih =>
    obtain ⟨b,hb,hbb⟩ := body_executes g (List.replicate m true) d q r hd hr
    obtain ⟨t,ht,htb⟩ := ih (stepQR d q r).1 (stepQR d q r).2 (stepQR_remainder d q r hd hr)
    have hs : Function.update (store (List.replicate (m+1) true) d q r (List.replicate (d-r) true)) 0
        (List.replicate m true)=store (List.replicate m true) d q r (List.replicate (d-r) true) := by
      funext i; fin_cases i <;> rfl
    rw [← hs] at hb
    refine ⟨1+b+1+t,WhileExecution.one rfl hb ht,?_⟩
    nlinarith

 theorem block_executes (g : BitString → ℕ) (m d : ℕ) (hd : 0<d) :
    ∃ t, block.Executes g (store (List.replicate m true) d 0 0 [])
      (store [] d (m/d) (m%d) []) t ∧ t≤m*(6*d+18)+6*d+8 := by
  have h1 : (copyOn (1 : Fin 6) 4 5 (by decide) (by decide) (by decide)).Executes g
      (store (List.replicate m true) d 0 0 [])
      (store (List.replicate m true) d 0 0 (List.replicate d true)) (5*d+2) := by
    convert copyOn_executes g (1 : Fin 6) 4 5 (by decide) (by decide) (by decide)
      (store (List.replicate m true) d 0 0 []) rfl using 1
    · funext i; fin_cases i <;> simp [store]
    · simp [store]
  obtain ⟨c,hc,hcb⟩ := loop_executes g m d 0 0 hd hd
  simp only [Nat.sub_zero,foldQR_correct m d hd] at hc
  have h3 : (clear (4 : Fin 6)).Executes g (store [] d (m/d) (m%d) (List.replicate (d-m%d) true))
      (store [] d (m/d) (m%d) []) (d-m%d+1) := by
    convert clear_executes g (4 : Fin 6) (store [] d (m/d) (m%d) (List.replicate (d-m%d) true)) using 1
    · funext i; fin_cases i <;> rfl
    · simp [store]
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g hc h3),?_⟩
  omega

 noncomputable def timeBound : Polynomial ℕ := 6*Polynomial.X^2+24*Polynomial.X+8
 theorem block_polynomial (g : BitString → ℕ) (m d : ℕ) (hd : 0<d) :
    ∃ t, block.Executes g (store (List.replicate m true) d 0 0 [])
      (store [] d (m/d) (m%d) []) t ∧ t≤timeBound.eval (m+d) := by
  obtain ⟨t,ht,hb⟩ := block_executes g m d hd
  refine ⟨t,ht,hb.trans ?_⟩
  simp only [timeBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_ofNat,Polynomial.eval_X]
  nlinarith

 lemma block_queryFree : block.QueryFree := by
  have hdrop : dropClock.QueryFree := by intro q i o next; fin_cases q <;> simp [machine,dropClock]
  have hcycle : completeCycle.QueryFree := seq_queryFree _ _ (push_queryFree _ _)
    (seq_queryFree _ _ (clear_queryFree _) (copyOn_queryFree _ _ _ _ _ _))
  have htest : testBoundary.QueryFree := branchPop_queryFree _ _ _ _ hcycle (push_queryFree _ _) (push_queryFree _ _)
  have hb : body.QueryFree := seq_queryFree _ _ hdrop (seq_queryFree _ _ (push_queryFree _ _) htest)
  exact seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (whilePop_queryFree _ _ _ hb hb) (clear_queryFree _))

 noncomputable def on {k : ℕ} (φ : Fin 6 ↪ Fin (k+1)) : OracleBlock k := rename block φ

 theorem on_executes {k : ℕ} (φ : Fin 6 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (m d : ℕ) (hd : 0<d) (hs : s∘φ=store (List.replicate m true) d 0 0 []) :
    ∃ t, (on φ).Executes g s
      (Function.update (Function.update (Function.update s (φ 0) [])
        (φ 2) (List.replicate (m/d) true)) (φ 3) (List.replicate (m%d) true)) t ∧
      t≤m*(6*d+18)+6*d+8 := by
  obtain ⟨t,ht,hb⟩ := block_executes g m d hd
  refine ⟨t,?_,hb⟩
  apply rename_executes_to block φ g ht hs
  · have he : (Function.update (Function.update (Function.update s (φ 0) [])
          (φ 2) (List.replicate (m/d) true)) (φ 3) (List.replicate (m%d) true))∘φ =
        Function.update (Function.update (Function.update (s∘φ) 0 [])
          2 (List.replicate (m/d) true)) 3 (List.replicate (m%d) true) := by
      funext i; simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i; fin_cases i <;> rfl
  · intro j hj
    rw [Function.update_of_ne (hj 3).symm,Function.update_of_ne (hj 2).symm,Function.update_of_ne (hj 0).symm]

 lemma on_queryFree {k : ℕ} (φ : Fin 6 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ block_queryFree

 theorem block_runs (g : BitString → ℕ) (m d : ℕ) (hd : 0<d) :
    ∃ (c : block.machine.Config) (t : ℕ), block.machine.Runs g
      (block.config block.start (store (List.replicate m true) d 0 0 [])) c t ∧
      c.stack=store [] d (m/d) (m%d) [] ∧ t≤timeBound.eval (m+d) := by
  obtain ⟨t,ht,hb⟩ := block_polynomial g m d hd
  refine ⟨block.config block.exit (store [] d (m/d) (m%d) []),t,?_,rfl,hb⟩
  apply (runs_iff_steps_halt _).mpr
  exact ⟨ht,by simp [OracleMachine.step,machine,config,block.exit_halt]⟩

end HiddenCircuits.Complexity.UnaryDivision
