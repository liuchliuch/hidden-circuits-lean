import HiddenCircuits.Approximation.SamplerRuntime.PartnerInitialized
import HiddenCircuits.Complexity.OracleMove
import HiddenCircuits.Complexity.PolynomialBounds

/-! Literal fixed-seventy-eight-stack preparation of the general sampler.

The graph parser has preserved the raw graph, extracted its matrix payload and
unary vertex count, and retained the input-size cap and random tape. This block
moves the payload and tape to the partner runner's ports, constructs the unary
clock `3*(M+1)^4`, and consumes exactly that many tape positions. Missing random
bits are padded with false, as in the total functional sampler. Every scratch
port is empty at the boundary to the concrete initializer; no graph validity
assumption or execution certificate is used here.
-/
namespace HiddenCircuits.Approximation.SamplerRuntime.GraphOuterCorePreparation
open Complexity Complexity.OracleBlock Polynomial
set_option maxHeartbeats 1000000

abbrev unary (n : ℕ) : BitString := List.replicate n true

/-- A fully specified store: every port not listed is empty. -/
def workingStore (a b d e f j clock cap init : BitString) (n : ℕ) : Store 77 := fun i =>
  if i.val=0 then a else if i.val=1 then b else if i.val=3 then unary n
  else if i.val=4 then d else if i.val=5 then e else if i.val=6 then f
  else if i.val=9 then j else if i.val=27 then clock else if i.val=28 then cap
  else if i.val=29 then init else []

/-- Successful outer-parser boundary: tape0, payload1, n3, raw graph4, M6. -/
def entryStore (rawGraph payload : BitString) (n M : ℕ) (tape : BitString) : Store 77 :=
  workingStore tape payload rawGraph [] (unary M) [] [] [] [] n

/-- Exact initializer boundary, including the disjoint chain suffix. -/
def targetStore (payload : BitString) (n M : ℕ) (tape : BitString) : Store 77 :=
  PartnerInitialized.stageStore (extra:=48)
    (PartnerRunner.state payload n (M+1) (tape.drop (3*(M+1)^4)) [] [] [])
    (TapeRead.takePadded (3*(M+1)^4) tape)

noncomputable def setup : OracleBlock 77 :=
  seq (copyOn 6 28 9 (by decide) (by decide) (by decide))
    (seq (push 28 true) (seq (clear 6)
      (seq (moveOn 0 5 9 (by decide) (by decide) (by decide))
        (seq (moveOn 1 0 9 (by decide) (by decide) (by decide)) (clear 4)))))

def clockPorts : Fin 5 ↪ Fin 78 where
  toFun i := ![28,27,6,7,8] i
  inj' := by decide +kernel

def tapePorts : Fin 3 ↪ Fin 78 where
  toFun i := ![5,27,9] i
  inj' := by decide +kernel

noncomputable def clockPolynomial : Polynomial ℕ := 3*X^4
noncomputable def clock : OracleBlock 77 :=
  rename (UnaryPolynomial.polynomialBlock clockPolynomial) clockPorts
noncomputable def readTape : OracleBlock 77 := TapeRead.on tapePorts
noncomputable def restoreOrder : OracleBlock 77 := reverseOn 9 29 (by decide)
noncomputable def program : OracleBlock 77 := seq setup (seq clock (seq readTape restoreOrder))

/-- Polynomial part of the cost; linear movement of input data is charged
separately. The evaluator is an actual unary finite-stack program. -/
noncomputable def time : Polynomial ℕ :=
  UnaryPolynomial.polynomialTime clockPolynomial+21*X^4+40

lemma clockPolynomial_eval (N : ℕ) : clockPolynomial.eval N=3*N^4 := by
  simp [clockPolynomial]

lemma setup_executes (g : BitString → ℕ) (rawGraph payload : BitString)
    (n M : ℕ) (tape : BitString) :
    setup.Executes g (entryStore rawGraph payload n M tape)
      (workingStore payload [] [] tape [] [] [] (unary (M+1)) [] n)
      (6*M+6*tape.length+6*payload.length+rawGraph.length+25) := by
  let s0 := entryStore rawGraph payload n M tape
  let s1 := workingStore tape payload rawGraph [] (unary M) [] [] (unary M) [] n
  let s2 := workingStore tape payload rawGraph [] (unary M) [] [] (unary (M+1)) [] n
  let s3 := workingStore tape payload rawGraph [] [] [] [] (unary (M+1)) [] n
  let s4 := workingStore [] payload rawGraph tape [] [] [] (unary (M+1)) [] n
  let s5 := workingStore payload [] rawGraph tape [] [] [] (unary (M+1)) [] n
  let s6 := workingStore payload [] [] tape [] [] [] (unary (M+1)) [] n
  have h1 : (copyOn (6:Fin 78) 28 9 (by decide) (by decide) (by decide)).Executes g s0 s1 (5*M+2) := by
    convert copyOn_executes g (6:Fin 78) 28 9 (by decide) (by decide) (by decide) s0 rfl using 1
    · funext i;fin_cases i <;> simp [s0,s1,entryStore,workingStore]
    · simp [s0,entryStore,workingStore]
  have h2 : (push (28:Fin 78) true).Executes g s1 s2 1 := by
    convert push_executes g (28:Fin 78) true s1 using 1
    funext i;fin_cases i <;> simp [s1,s2,workingStore,List.replicate_succ]
  have h3 : (clear (6:Fin 78)).Executes g s2 s3 (M+1) := by
    convert clear_executes g (6:Fin 78) s2 using 1
    · funext i;fin_cases i <;> simp [s2,s3,workingStore]
    · simp [s2,workingStore]
  have h4 : (moveOn (0:Fin 78) 5 9 (by decide) (by decide) (by decide)).Executes g s3 s4 (6*tape.length+5) := by
    convert moveOn_executes g (0:Fin 78) 5 9 (by decide) (by decide) (by decide) s3 rfl using 1
    funext i;fin_cases i <;> simp [s3,s4,workingStore]
  have h5 : (moveOn (1:Fin 78) 0 9 (by decide) (by decide) (by decide)).Executes g s4 s5 (6*payload.length+5) := by
    convert moveOn_executes g (1:Fin 78) 0 9 (by decide) (by decide) (by decide) s4 rfl using 1
    funext i;fin_cases i <;> simp [s4,s5,workingStore]
  have h6 : (clear (4:Fin 78)).Executes g s5 s6 (rawGraph.length+1) := by
    convert clear_executes g (4:Fin 78) s5 using 1
    funext i;fin_cases i <;> simp [s5,s6,workingStore]
  have h := seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3
    (seq_executes _ _ g h4 (seq_executes _ _ g h5 h6))))
  convert h using 1
  ring

lemma clock_executes (g : BitString → ℕ) (payload : BitString) (n N : ℕ) (tape : BitString) :
    clock.Executes g (workingStore payload [] [] tape [] [] [] (unary N) [] n)
      (workingStore payload [] [] tape [] [] (unary (3*N^4)) (unary N) [] n)
      ((UnaryPolynomial.polynomialTime clockPolynomial).eval N) := by
  have h := UnaryPolynomial.polynomialOn_executes clockPorts g clockPolynomial N
    (workingStore payload [] [] tape [] [] [] (unary N) [] n)
    (by funext i;fin_cases i <;> rfl)
  rw [clockPolynomial_eval] at h
  convert h using 1
  funext i;fin_cases i <;> rfl

lemma readTape_executes (g : BitString → ℕ) (payload : BitString) (n N : ℕ) (tape : BitString) :
    readTape.Executes g
      (workingStore payload [] [] tape [] [] (unary (3*N^4)) (unary N) [] n)
      (workingStore payload [] [] (tape.drop (3*N^4)) []
        (TapeRead.takePadded (3*N^4) tape).reverse [] (unary N) [] n)
      (5*(3*N^4)+1) := by
  convert TapeRead.on_executes tapePorts g
    (workingStore payload [] [] tape [] [] (unary (3*N^4)) (unary N) [] n)
    (workingStore payload [] [] (tape.drop (3*N^4)) []
      (TapeRead.takePadded (3*N^4) tape).reverse [] (unary N) [] n)
    tape (unary (3*N^4)) []
    (by funext i;fin_cases i <;> rfl)
    (by funext i;fin_cases i <;> simp [workingStore,tapePorts,TapeRead.state])
    (by
      intro i hi
      have h5 : i.val≠5 := by intro h;apply hi 0;exact Fin.ext h.symm
      have h9 : i.val≠9 := by intro h;apply hi 2;exact Fin.ext h.symm
      have h27 : i.val≠27 := by intro h;apply hi 1;exact Fin.ext h.symm
      simp [workingStore,h5,h9,h27]) using 1
  simp

lemma restoreOrder_executes (g : BitString → ℕ) (payload : BitString) (n N : ℕ) (tape : BitString) :
    restoreOrder.Executes g
      (workingStore payload [] [] (tape.drop (3*N^4)) []
        (TapeRead.takePadded (3*N^4) tape).reverse [] (unary N) [] n)
      (workingStore payload [] [] (tape.drop (3*N^4)) [] [] [] (unary N)
        (TapeRead.takePadded (3*N^4) tape) n)
      (2*(3*N^4)+1) := by
  convert reverseOn_executes g (9:Fin 78) 29 (by decide)
    (workingStore payload [] [] (tape.drop (3*N^4)) []
      (TapeRead.takePadded (3*N^4) tape).reverse [] (unary N) [] n) using 1
  · funext i;fin_cases i <;> simp [workingStore]
  · simp [workingStore,TapeRead.prefix_length]

lemma targetStore_eq (payload : BitString) (n M : ℕ) (tape : BitString) :
    targetStore payload n M tape=
      workingStore payload [] [] (tape.drop (3*(M+1)^4)) [] [] [] (unary (M+1))
        (TapeRead.takePadded (3*(M+1)^4) tape) n := by
  funext i;fin_cases i <;> rfl

/-- Total execution, for every raw tape including empty and insufficient tapes,
with the exact clean initializer state and a closed charged running-time bound. -/
theorem program_executes (g : BitString → ℕ) (rawGraph payload : BitString)
    (n M : ℕ) (tape : BitString) :
    ∃cost,program.Executes g (entryStore rawGraph payload n M tape)
      (PartnerInitialized.stageStore (extra:=48)
        (PartnerRunner.state payload n (M+1) (tape.drop (3*(M+1)^4)) [] [] [])
        (TapeRead.takePadded (3*(M+1)^4) tape)) cost ∧
      cost≤time.eval (M+1)+20*(rawGraph.length+payload.length+tape.length+M+1) := by
  have h := seq_executes _ _ g (setup_executes g rawGraph payload n M tape)
    (seq_executes _ _ g (clock_executes g payload n (M+1) tape)
      (seq_executes _ _ g (readTape_executes g payload n (M+1) tape)
        (restoreOrder_executes g payload n (M+1) tape)))
  change program.Executes g _ (workingStore _ _ _ _ _ _ _ _ _ _) _ at h
  rw [←targetStore_eq] at h
  refine ⟨_,h,?_⟩
  simp only [time,eval_add,eval_mul,eval_pow,eval_X,eval_ofNat]
  omega

/-- A closed natural-coefficient polynomial under a common input/tape cap. -/
noncomputable def capTime : Polynomial ℕ := time+80*X

/-- Convenience form for the outer total bit-machine runtime: a single cap
bounds all moved strings and the successor precision/input-size parameter. -/
theorem program_executes_cap (g : BitString → ℕ) (rawGraph payload : BitString)
    (n M : ℕ) (tape : BitString) (C : ℕ)
    (hr : rawGraph.length≤C) (hp : payload.length≤C) (ht : tape.length≤C) (hM : M+1≤C) :
    ∃cost,program.Executes g (entryStore rawGraph payload n M tape)
      (targetStore payload n M tape) cost ∧ cost≤capTime.eval C := by
  obtain ⟨c,hc,hb⟩ := program_executes g rawGraph payload n M tape
  refine ⟨c,hc,?_⟩
  have htime := polynomial_nat_eval_mono time hM
  change time.eval (M+1)≤time.eval C at htime
  simp only [capTime,eval_add,eval_mul,eval_ofNat,eval_X]
  omega

lemma setup_queryFree : setup.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (push_queryFree _ _) (seq_queryFree _ _ (clear_queryFree _)
    (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _)
      (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _) (clear_queryFree _)))))

lemma program_queryFree : program.QueryFree := seq_queryFree _ _ setup_queryFree
  (seq_queryFree _ _ (rename_queryFree _ _ (UnaryPolynomial.polynomialBlock_queryFree _))
    (seq_queryFree _ _ (TapeRead.on_queryFree _) (reverseOn_queryFree _ _ _)))

/-- No residue survives outside the five documented output ports. -/
lemma targetStore_clean (payload : BitString) (n M : ℕ) (tape : BitString) (i : Fin 78)
    (h0 : i.val≠0) (h3 : i.val≠3) (h5 : i.val≠5) (h28 : i.val≠28) (h29 : i.val≠29) :
    targetStore payload n M tape i=[] := by
  rw [targetStore_eq]
  simp [workingStore,h0,h3,h5,h28,h29]

/-- Canonical sufficiently long random tapes use their ordinary prefix. -/
lemma targetStore_of_long_tape (payload : BitString) (n M : ℕ) (tape : BitString)
    (htape : 3*(M+1)^4≤tape.length) :
    targetStore payload n M tape=
      PartnerInitialized.stageStore (extra:=48)
        (PartnerRunner.state payload n (M+1) (tape.drop (3*(M+1)^4)) [] [] [])
        (tape.take (3*(M+1)^4)) := by
  unfold targetStore
  rw [TapeRead.prefix_eq_take _ _ htape]

end HiddenCircuits.Approximation.SamplerRuntime.GraphOuterCorePreparation
