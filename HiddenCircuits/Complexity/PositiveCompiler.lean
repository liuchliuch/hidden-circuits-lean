import HiddenCircuits.Complexity.CompilerFinal
import HiddenCircuits.Complexity.InitialRowCorrectness

/-! The complete positive-case finite-bit verifier-to-CNF compiler. Every stage
is real code with proved executions; polynomial time is assembled from those
executions, and the final bytes equal the actual count-preserving CNF encoding. -/
namespace HiddenCircuits.Complexity.PositiveCompiler
open OracleBlock Polynomial TM2BooleanEncoding CompilerState
variable {v : BitString → Bool}
variable (M : Turing.TM2ComputableInPolyTime id Computability.encodeBool v) (p : Polynomial ℕ)

noncomputable def dimensions (x : BitString) : Registers :=
  let m := p.eval x.length
  let T := VerifierTableau.horizon M x m
  let H := VerifierTableau.height M x m
  let C := bitCount M.tm H
  {clock:=T,height:=H,cells:=C,witnesses:=m,varCount:=m+(T+1)*C}

noncomputable def afterHeader (x : BitString) : Registers :=
  let R := dimensions M p x
  {R with varCount:=0,stream:=(headerBits R.varCount).reverse}
noncomputable def afterInitial (x : BitString) : Registers :=
  let R := afterHeader M p x
  {R with stream:=(InitialRowEmitter.bits M x R.witnesses R.height).reverse++R.stream}
noncomputable def afterBases (x : BitString) : Registers :=
  let R := afterInitial M p x
  {R with base:=R.witnesses,nextBase:=R.witnesses+R.cells}
noncomputable def afterTransitions (x : BitString) : Registers :=
  let R := afterBases M p x
  {R with base:=R.base+R.clock*R.cells,nextBase:=R.nextBase+R.clock*R.cells,clock:=0, stream:=(TimeEmitter.bits M.tm R.height R.cells R.base R.nextBase R.clock).reverse++R.stream}
noncomputable def afterAccept (ht : VerifierTableau.HasTrueSymbol M) (x : BitString) : Registers :=
  let R := afterTransitions M p x
  {R with stream:=(serializedClause [(R.base+VerifierTableau.outputOffset M ht,true)]).reverse++R.stream}

noncomputable def core (ht : VerifierTableau.HasTrueSymbol M) : OracleBlock 17 :=
  seq (VerifierSetup.program M p) (seq header (seq (initialClean M)
    (seq bases (seq (transitions M) (accept (VerifierTableau.outputOffset M ht))))))

noncomputable def coreTime (ht : VerifierTableau.HasTrueSymbol M) : Polynomial ℕ :=
  let T := VerifierTableau.horizonPolynomial M p
  let H := VerifierTableau.heightPolynomial M p
  let C := VerifierTableau.cellsPolynomial M p
  VerifierSetup.time M p+(9*VerifierSetup.variablesPolynomial M p+4)+
    (InitialRowEmitter.cleanTime M).comp (X+p+H)+(10*p+5*C+10)+
    (TimeEmitter.time M.tm).comp (H+p+(p+C)+T+C)+
    (acceptTime (VerifierTableau.outputOffset M ht)).comp (p+T*C)+10

lemma setup_executes (g : BitString → ℕ) (x : BitString) :
    (VerifierSetup.program M p).Executes g (Function.update (fun _ => []) 0 x)
      (store x (dimensions M p x)) ((VerifierSetup.time M p).eval x.length) := by
  have h := VerifierSetup.program_executes M p g x
  convert h using 1
  funext i;fin_cases i <;> simp [store,dimensions,VerifierSetup.state,VerifierSetup.polynomial,
    VerifierSetup.variablesPolynomial,VerifierTableau.heightPolynomial_eval,VerifierTableau.cellsPolynomial_eval,
    VerifierTableau.horizonPolynomial_eval]

/-- The complete emitting prefix, before final reversal. -/
theorem core_executes (g : BitString → ℕ) (ht : VerifierTableau.HasTrueSymbol M) (x : BitString) :
    ∃ cost, (core M p ht).Executes g (Function.update (fun _ => []) 0 x)
      (store x (afterAccept M p ht x)) cost ∧ cost ≤ (coreTime M p ht).eval x.length := by
  have h₀ := setup_executes M p g x
  have h₁ : header.Executes g (store x (dimensions M p x)) (store x (afterHeader M p x))
      (9*(dimensions M p x).varCount+4) := by
    simpa only [afterHeader,dimensions,List.append_nil] using header_executes g x (dimensions M p x)
  have hH : 2*x.length+(afterHeader M p x).witnesses+1≤(afterHeader M p x).height := by
    change 2*x.length+p.eval x.length+1 ≤ VerifierTableau.height M x (p.eval x.length)
    unfold VerifierTableau.height;omega
  obtain ⟨ci,hi,hbi⟩ := initialClean_executes M g x (afterHeader M p x) rfl rfl rfl rfl rfl hH
  have h₂ : (initialClean M).Executes g (store x (afterHeader M p x)) (store x (afterInitial M p x)) ci := hi
  have h₃ : bases.Executes g (store x (afterInitial M p x)) (store x (afterBases M p x))
      (10*(dimensions M p x).witnesses+5*(dimensions M p x).cells+10) := by
    simpa [afterBases,afterInitial,afterHeader,dimensions,Nat.add_comm] using bases_executes g x (afterInitial M p x)
  obtain ⟨ct,htime,hbt⟩ := transitions_executes M g x (afterBases M p x) rfl rfl
    (VerifierTableau.height_positive M x (p.eval x.length))
  have h₄ : (transitions M).Executes g (store x (afterBases M p x)) (store x (afterTransitions M p x)) ct := htime
  obtain ⟨ca,ha,hba⟩ := accept_executes g (VerifierTableau.outputOffset M ht) x (afterTransitions M p x) rfl
  have h₅ : (accept (VerifierTableau.outputOffset M ht)).Executes g
      (store x (afterTransitions M p x)) (store x (afterAccept M p ht x)) ca := ha
  have he := seq_executes _ _ g h₀ (seq_executes _ _ g h₁ (seq_executes _ _ g h₂
    (seq_executes _ _ g h₃ (seq_executes _ _ g h₄ h₅))))
  refine ⟨_,he,?_⟩
  dsimp only [afterHeader,afterInitial,afterBases,afterTransitions,dimensions] at hbi hbt hba
  simp only [coreTime,VerifierSetup.variablesPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_comp,Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one,
    VerifierTableau.heightPolynomial_eval,VerifierTableau.cellsPolynomial_eval,VerifierTableau.horizonPolynomial_eval]
  dsimp only [dimensions]
  omega

/-- All four stream segments are linked to the actual binary formula. -/
theorem stream_correct (ht : VerifierTableau.HasTrueSymbol M) (x : BitString) :
    (afterAccept M p ht x).stream =
      (VerifierTableau.uniformPositiveFormula M x (p.eval x.length) ht).bits.reverse := by
  have hI := InitialRowEmitter.bits_eq_initialStream M x (p.eval x.length)
    (VerifierTableau.height M x (p.eval x.length)) (VerifierTableau.horizon M x (p.eval x.length))
    (by unfold VerifierTableau.height;omega)
  rw [InitialRowEmitter.initialSources_eq] at hI
  rw [VerifierTableau.uniformPositiveFormula_stream]
  simp [afterAccept,afterTransitions,afterBases,afterInitial,afterHeader,dimensions,headerBits,hI,
    List.reverse_append,List.append_assoc]

noncomputable def program (ht : VerifierTableau.HasTrueSymbol M) : OracleBlock 17 := seq (core M p ht) finish
noncomputable def time (ht : VerifierTableau.HasTrueSymbol M) : Polynomial ℕ :=
  coreTime M p ht+2*VerifierTableau.formulaSizePolynomial M p+3

/-- Actual complete bit-stack computation of the concrete CNF input, with a
proved polynomial runtime for every original binary input. -/
theorem program_executes (g : BitString → ℕ) (ht : VerifierTableau.HasTrueSymbol M) (x : BitString) :
    ∃ s : Store 17, ∃ cost, (program M p ht).Executes g (Function.update (fun _ => []) 0 x) s cost ∧
      s 0 = (VerifierTableau.uniformPositiveFormula M x (p.eval x.length) ht).bits ∧
      cost ≤ (time M p ht).eval x.length := by
  obtain ⟨c,hc,hb⟩ := core_executes M p g ht x
  have hf := finish_executes g x (afterAccept M p ht x) rfl
  have hout := seq_executes _ _ g hc hf
  have hs := stream_correct M p ht x
  have hsize := VerifierTableau.uniformFormula_polynomial_size M p x
  rw [VerifierTableau.uniformFormula_pos M x _ ht] at hsize
  change (VerifierTableau.uniformPositiveFormula M x (p.eval x.length) ht).bits.length ≤ _ at hsize
  refine ⟨finishedStore x (afterAccept M p ht x),_,hout,?_,?_⟩
  · simp [hs]
  · rw [hs,List.length_reverse]
    simp only [time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
    omega

lemma core_queryFree (ht : VerifierTableau.HasTrueSymbol M) : (core M p ht).QueryFree :=
  seq_queryFree _ _ (VerifierSetup.program_queryFree M p) (seq_queryFree _ _ header_queryFree
    (seq_queryFree _ _ (initialClean_queryFree M) (seq_queryFree _ _ bases_queryFree
      (seq_queryFree _ _ (transitions_queryFree M) (accept_queryFree _)))))
lemma program_queryFree (ht : VerifierTableau.HasTrueSymbol M) : (program M p ht).QueryFree :=
  seq_queryFree _ _ (core_queryFree M p ht) finish_queryFree

end HiddenCircuits.Complexity.PositiveCompiler
