import HiddenCircuits.Complexity.PositiveCompiler

/-! Actual finite compiler for the degenerate verifier whose reachable alphabet
contains no true output symbol. It emits one empty clause, preserving zero count. -/
namespace HiddenCircuits.Complexity.NegativeCompiler
open OracleBlock Polynomial CompilerState
variable {v : BitString → Bool}
variable (M : Turing.TM2ComputableInPolyTime id Computability.encodeBool v) (p : Polynomial ℕ)

noncomputable def emptyClause : OracleBlock 17 := seq (push 6 true) (push 6 false)

theorem emptyClause_executes (g : BitString → ℕ) (x : BitString) (R : Registers) :
    emptyClause.Executes g (store x R)
      (store x {R with stream:=(serializedClause []).reverse++R.stream}) 4 := by
  have h₁ : (push (6 : Fin 18) true).Executes g (store x R) (store x {R with stream:=true::R.stream}) 1 := by
    simpa only [update_stream] using push_executes g (6 : Fin 18) true (store x R)
  have h₂ : (push (6 : Fin 18) false).Executes g (store x {R with stream:=true::R.stream})
      (store x {R with stream:=(serializedClause []).reverse++R.stream}) 1 := by
    simpa [update_stream,serializedClause] using push_executes g (6 : Fin 18) false (store x {R with stream:=true::R.stream})
  exact seq_executes _ _ g h₁ h₂

noncomputable def afterClear (x : BitString) : Registers := {PositiveCompiler.dimensions M p x with varCount:=0}
noncomputable def afterCopy (x : BitString) : Registers := {afterClear M p x with varCount:=p.eval x.length}
noncomputable def afterHeader (x : BitString) : Registers :=
  {afterCopy M p x with varCount:=0,stream:=(headerBits (p.eval x.length)).reverse}
noncomputable def afterClause (x : BitString) : Registers :=
  {afterHeader M p x with stream:=(serializedClause []).reverse++(afterHeader M p x).stream}

noncomputable def core : OracleBlock 17 := seq (VerifierSetup.program M p) (seq (clear 14)
  (seq (copyOn 13 14 4 (by decide) (by decide) (by decide)) (seq header emptyClause)))
noncomputable def coreTime : Polynomial ℕ :=
  VerifierSetup.time M p+VerifierSetup.variablesPolynomial M p+14*p+19

theorem core_executes (g : BitString → ℕ) (x : BitString) :
    (core M p).Executes g (Function.update (fun _ => []) 0 x) (store x (afterClause M p x))
      ((coreTime M p).eval x.length) := by
  have h₀ := PositiveCompiler.setup_executes M p g x
  have h₁ : (clear (14 : Fin 18)).Executes g (store x (PositiveCompiler.dimensions M p x))
      (store x (afterClear M p x)) ((PositiveCompiler.dimensions M p x).varCount+1) := by
    have h := clear_executes g (14 : Fin 18) (store x (PositiveCompiler.dimensions M p x))
    convert h using 1
    · funext i;fin_cases i <;> simp [store,afterClear]
    · simp [store]
  have h₂ : (copyOn (13 : Fin 18) 14 4 (by decide) (by decide) (by decide)).Executes g
      (store x (afterClear M p x)) (store x (afterCopy M p x)) (5*p.eval x.length+2) := by
    have h := copyOn_executes g (13 : Fin 18) 14 4 (by decide) (by decide) (by decide) (store x (afterClear M p x)) rfl
    convert h using 1
    · funext i;fin_cases i <;> simp [store,afterCopy,afterClear,PositiveCompiler.dimensions]
    · simp [store,afterClear,PositiveCompiler.dimensions]
  have h₃ : header.Executes g (store x (afterCopy M p x)) (store x (afterHeader M p x)) (9*p.eval x.length+4) := by
    simpa [afterHeader,afterCopy,afterClear,PositiveCompiler.dimensions] using header_executes g x (afterCopy M p x)
  have h₄ : emptyClause.Executes g (store x (afterHeader M p x)) (store x (afterClause M p x)) 4 :=
    emptyClause_executes g x (afterHeader M p x)
  have he := seq_executes _ _ g h₀ (seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ h₄)))
  convert he using 1
  simp [coreTime,VerifierSetup.variablesPolynomial,PositiveCompiler.dimensions,
    VerifierTableau.horizonPolynomial_eval,VerifierTableau.cellsPolynomial_eval]
  ring

lemma rejecting_bits (m : ℕ) : (rejectingCNF m).bits = headerBits m++serializedClause [] := by
  simp [rejectingCNF,CNF.bits,CNF.clauseBits,encodeBitList,headerBits,serializedClause,
    pairBits_escape,escapeBits_replicate_true,escapeBits]

lemma stream_correct (x : BitString) : (afterClause M p x).stream = (rejectingCNF (p.eval x.length)).bits.reverse := by
  rw [rejecting_bits]
  simp [afterClause,afterHeader,List.reverse_append]

noncomputable def program : OracleBlock 17 := seq (core M p) finish
noncomputable def time : Polynomial ℕ := VerifierSetup.time M p+VerifierSetup.variablesPolynomial M p+18*p+28

theorem program_executes (g : BitString → ℕ) (x : BitString) :
    ∃ s : Store 17, ∃ cost, (program M p).Executes g (Function.update (fun _ => []) 0 x) s cost ∧
      s 0 = (rejectingCNF (p.eval x.length)).bits ∧ cost ≤ (time M p).eval x.length := by
  have hc := core_executes M p g x
  have hf := finish_executes g x (afterClause M p x) rfl
  refine ⟨finishedStore x (afterClause M p x),_,seq_executes _ _ g hc hf,?_,?_⟩
  · simp [stream_correct]
  · rw [stream_correct,List.length_reverse,rejectingCNF_bits]
    simp [time,coreTime]
    omega

lemma program_queryFree : (program M p).QueryFree :=
  seq_queryFree _ _ (seq_queryFree _ _ (VerifierSetup.program_queryFree M p)
    (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
      (seq_queryFree _ _ header_queryFree (seq_queryFree _ _ (push_queryFree _ _) (push_queryFree _ _)))))) finish_queryFree

end HiddenCircuits.Complexity.NegativeCompiler
