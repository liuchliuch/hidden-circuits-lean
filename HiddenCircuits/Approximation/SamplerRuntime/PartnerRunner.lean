import HiddenCircuits.Approximation.SamplerRuntime.PartnerIteration
import HiddenCircuits.Approximation.SamplerRuntime.PartnerBudget
import HiddenCircuits.Approximation.SamplerRuntime.PartnerOutput
import HiddenCircuits.Approximation.SamplerRuntime.ProposalWidth

/-! Physical mixing stage after a sound initializer has returned a partner
witness. The public sampler must compose this internal stage with initialization. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.PartnerRunner
open Complexity Complexity.OracleBlock Polynomial

abbrev unary (n : ℕ) : BitString := List.replicate n true

def state (graph : BitString) (n N : ℕ) (tape data width clock : BitString) : Store 28 := fun r =>
  if r.val=0 then graph else if r.val=2 then data else if r.val=3 then unary n
  else if r.val=4 then width else if r.val=5 then tape else if r.val=27 then clock
  else if r.val=28 then unary N else []

def widthPorts : Fin 6 ↪ Fin 29 where
  toFun i := ![3,6,4,7,8,9] i
  inj' := by decide +kernel

def clockPorts : Fin 5 ↪ Fin 29 where
  toFun i := ![28,27,6,7,8] i
  inj' := by decide +kernel

def iterationPorts : Fin 28 ↪ Fin 29 := ⟨Fin.castSucc,Fin.castSucc_injective 28⟩
noncomputable def width : OracleBlock 28 := ProposalWidth.on widthPorts
noncomputable def clock : OracleBlock 28 := rename (UnaryPolynomial.polynomialBlock PartnerBudget.stepsPolynomial) clockPorts
noncomputable def iteration : OracleBlock 28 := rename PartnerIteration.program iterationPorts
noncomputable def program : OracleBlock 28 := seq width (seq clock (seq iteration (push 2 true)))

variable {n : ℕ}

def evaluate (G : MatrixGraph n) (N : ℕ) (P : PerfectPartner G.graph) (tape : BitString) : BitString :=
  PartnerOutput.success G (PartnerIteration.iterate G (PartnerBudget.steps N) P tape)

noncomputable def time : Polynomial ℕ := 40*(X+1)^2+UnaryPolynomial.polynomialTime PartnerBudget.stepsPolynomial+
  PartnerBudget.stepsPolynomial*(6000000*(X+1)^4+2)+8

lemma width_executes (g : BitString → ℕ) (graph : BitString) (n N : ℕ) (tape data : BitString) :
    ∃t,width.Executes g (state graph n N tape data [] [])
      (state graph n N tape data (unary (Nat.size n)) []) t ∧ t≤40*(n+1)^2 := by
  obtain ⟨t,ht,hb⟩ := ProposalWidth.on_executes widthPorts g (state graph n N tape data [] []) (unary n)
    (by funext r;fin_cases r <;> rfl)
  refine ⟨t,?_,by simpa using hb⟩
  convert ht using 1
  funext r;fin_cases r <;> simp [state,widthPorts]

lemma clock_executes (g : BitString → ℕ) (graph : BitString) (n N : ℕ) (tape data : BitString) :
    clock.Executes g (state graph n N tape data (unary (Nat.size n)) [])
      (state graph n N tape data (unary (Nat.size n)) (unary (PartnerBudget.steps N)))
      ((UnaryPolynomial.polynomialTime PartnerBudget.stepsPolynomial).eval N) := by
  have h := UnaryPolynomial.polynomialOn_executes clockPorts g PartnerBudget.stepsPolynomial N
    (state graph n N tape data (unary (Nat.size n)) []) (by funext r;fin_cases r <;> rfl)
  rw [PartnerBudget.steps_eval] at h
  convert h using 1
  funext r;fin_cases r <;> rfl

lemma iteration_executes (g : BitString → ℕ) (G : MatrixGraph n) (N : ℕ)
    (P : PerfectPartner G.graph) (tape : BitString) :
    ∃t,iteration.Executes g
      (state G.bits n N tape (PartnerOutput.witness G P) (unary (Nat.size n)) (unary (PartnerBudget.steps N)))
      (state G.bits n N (tape.drop (PartnerIteration.width n*PartnerBudget.steps N))
        (PartnerOutput.witness G (PartnerIteration.iterate G (PartnerBudget.steps N) P tape)) (unary (Nat.size n)) []) t ∧
      t≤PartnerBudget.steps N*(6000000*(n+1)^4+2)+1 := by
  obtain ⟨t,ht,hb⟩ := PartnerIteration.program_executes g G P tape (unary (PartnerBudget.steps N))
  refine ⟨t,?_,by simpa using hb⟩
  apply rename_executes_to PartnerIteration.program iterationPorts g ht
  · funext r;fin_cases r <;> rfl
  · funext r;fin_cases r <;> simp [state,iterationPorts,PartnerIteration.state,PartnerStep.state,PartnerOutput.witness]
  · intro r hr;fin_cases r <;> first | rfl | exact (hr 2 rfl).elim | exact (hr 5 rfl).elim | exact (hr 27 rfl).elim

/-- Actual fixed twenty-nine-stack mixing stage, with physically evaluated
polynomial iteration clock and every fair-tape access charged. -/
theorem program_executes (g : BitString → ℕ) (G : MatrixGraph n) (N : ℕ) (hn : n≤N)
    (P : PerfectPartner G.graph) (tape : BitString) :
    ∃t,program.Executes g (state G.bits n N tape (PartnerOutput.witness G P) [] [])
      (state G.bits n N (tape.drop (PartnerIteration.width n*PartnerBudget.steps N))
        (evaluate G N P tape) (unary (Nat.size n)) []) t ∧ t≤time.eval N := by
  obtain ⟨a,ha,hba⟩ := width_executes g G.bits n N tape (PartnerOutput.witness G P)
  have hb := clock_executes g G.bits n N tape (PartnerOutput.witness G P)
  obtain ⟨c,hc,hbc⟩ := iteration_executes g G N P tape
  have hd : (push (2:Fin 29) true).Executes g
      (state G.bits n N (tape.drop (PartnerIteration.width n*PartnerBudget.steps N))
        (PartnerOutput.witness G (PartnerIteration.iterate G (PartnerBudget.steps N) P tape)) (unary (Nat.size n)) [])
      (state G.bits n N (tape.drop (PartnerIteration.width n*PartnerBudget.steps N))
        (evaluate G N P tape) (unary (Nat.size n)) []) 1 := by
    convert push_executes g (2:Fin 29) true
      (state G.bits n N (tape.drop (PartnerIteration.width n*PartnerBudget.steps N))
        (PartnerOutput.witness G (PartnerIteration.iterate G (PartnerBudget.steps N) P tape)) (unary (Nat.size n)) []) using 1
    funext r;fin_cases r <;> rfl
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb (seq_executes _ _ g hc hd)),?_⟩
  have hp2 := Nat.pow_le_pow_left (show n+1≤N+1 by omega) 2
  have hp4 := Nat.pow_le_pow_left (show n+1≤N+1 by omega) 4
  have hm := Nat.mul_le_mul_left (PartnerBudget.steps N) (show 6000000*(n+1)^4+2≤6000000*(N+1)^4+2 by omega)
  simp only [time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,
    Polynomial.eval_ofNat,Polynomial.eval_one,PartnerBudget.steps_eval]
  omega

lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (ProposalWidth.on_queryFree _)
  (seq_queryFree _ _ (rename_queryFree _ _ (UnaryPolynomial.polynomialBlock_queryFree _))
    (seq_queryFree _ _ (rename_queryFree _ _ PartnerIteration.program_queryFree) (push_queryFree _ _)))

noncomputable def on {k : ℕ} (φ : Fin 29 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 29 ↪ Fin (k+1)) (g : BitString → ℕ) (s t : Store k)
    (G : MatrixGraph n) (N : ℕ) (hn : n≤N) (P : PerfectPartner G.graph) (tape : BitString)
    (hs : s∘φ=state G.bits n N tape (PartnerOutput.witness G P) [] [])
    (ht : t∘φ=state G.bits n N (tape.drop (PartnerIteration.width n*PartnerBudget.steps N))
      (evaluate G N P tape) (unary (Nat.size n)) [])
    (hf : ∀r,(∀j,φ j≠r) → t r=s r) :
    ∃cost,(on φ).Executes g s t cost ∧ cost≤time.eval N := by
  obtain ⟨c,hc,hb⟩ := program_executes g G N hn P tape
  exact ⟨c,rename_executes_to program φ g hc hs ht hf,hb⟩

lemma on_queryFree {k : ℕ} (φ : Fin 29 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ program_queryFree

end HiddenCircuits.Approximation.SamplerRuntime.PartnerRunner
