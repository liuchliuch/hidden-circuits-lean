import HiddenCircuits.Approximation.SamplerRuntime.PartnerRunnerCorrectness

/-! Operational composition of initialization with the conditional mixing
continuation. Initialization is supplied by the caller of this modular contract. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.PartnerInitialized
open Complexity Complexity.OracleBlock Polynomial

abbrev Initializer := ∀{n : ℕ},(G : MatrixGraph n) → ℕ → BitString → Option (PerfectPartner G.graph)

def initialCode {n : ℕ} (G : MatrixGraph n) : Option (PerfectPartner G.graph) → BitString
  | none => []
  | some P => PartnerOutput.success G P

/-- Runner ports0..28 are fixed. Port29 carries the isolated initialization
random tape; higher ports are the initializer's own clean work bank. -/
def stageStore {extra : ℕ} (s : Store 28) (initTape : BitString) : Store (extra+29) := fun i =>
  if h : i.val<29 then s ⟨i.val,h⟩ else if i.val=29 then initTape else []

def runnerPorts (extra : ℕ) : Fin 29 ↪ Fin (extra+30) where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun z : Fin (extra+30) => z.val) h)

/-- This is the exact independent initializer interface still to be discharged:
actual instructions, bounded time, sound encoded result and no access to the
separate chain tape. The padding allowance includes cleanup of unused bits. -/
structure InitializerSpec {extra : ℕ} (B : OracleBlock (extra+29)) (p : Polynomial ℕ) (init : Initializer) : Prop where
  queryFree : B.QueryFree
  executes : ∀{n : ℕ}(g : BitString → ℕ)(G : MatrixGraph n)(N : ℕ), n≤N →
    ∀(initTape chainTape : BitString),initTape.length≤3*N^4 →
    ∃cost,B.Executes g (stageStore (PartnerRunner.state G.bits n N chainTape [] [] []) initTape)
      (stageStore (PartnerRunner.state G.bits n N chainTape (initialCode G (init G N initTape)) [] []) []) cost ∧
      cost≤p.eval N

noncomputable def mix (extra : ℕ) : OracleBlock (extra+29) := PartnerRunner.on (runnerPorts extra)
noncomputable def continuation (extra : ℕ) : OracleBlock (extra+29) := branchPop 2 skip (clear 2) (mix extra)
noncomputable def program {extra : ℕ} (B : OracleBlock (extra+29)) : OracleBlock (extra+29) := seq B (continuation extra)
noncomputable def time (p : Polynomial ℕ) : Polynomial ℕ := p+PartnerRunner.time+5

lemma mix_executes {extra n : ℕ} (g : BitString → ℕ) (G : MatrixGraph n) (N : ℕ) (hn : n≤N)
    (P : PerfectPartner G.graph) (chainTape : BitString) :
    ∃cost,(mix extra).Executes g
      (stageStore (PartnerRunner.state G.bits n N chainTape (PartnerOutput.witness G P) [] []) [])
      (stageStore (PartnerRunner.state G.bits n N (chainTape.drop (PartnerIteration.width n*PartnerBudget.steps N))
        (PartnerRunner.evaluate G N P chainTape) (PartnerRunner.unary (Nat.size n)) []) []) cost ∧
      cost≤PartnerRunner.time.eval N := by
  apply PartnerRunner.on_executes (runnerPorts extra) g _ _ G N hn P chainTape
  · funext i;simp [stageStore,runnerPorts,i.isLt]
  · funext i;simp [stageStore,runnerPorts,i.isLt]
  · intro i hi
    have hge : ¬i.val<29 := by
      intro h
      apply hi ⟨i.val,h⟩
      apply Fin.ext
      rfl
    simp [stageStore,hge]

lemma pop_success {extra n : ℕ} (G : MatrixGraph n) (N : ℕ) (P : PerfectPartner G.graph) (chainTape : BitString) :
    Function.update (stageStore (extra:=extra) (PartnerRunner.state G.bits n N chainTape (PartnerOutput.success G P) [] []) [])
      (2:Fin (extra+30)) (PartnerOutput.witness G P)=
    stageStore (PartnerRunner.state G.bits n N chainTape (PartnerOutput.witness G P) [] []) [] := by
  funext i
  by_cases h : i.val=2
  · have hi : i=(2:Fin (extra+30)) := Fin.ext h
    subst i
    rfl
  · have hi : i≠(2:Fin (extra+30)) := by
      intro hi
      apply h
      simpa [Nat.mod_eq_of_lt (show 2<extra+30 by omega)] using congrArg (fun x : Fin (extra+30) => x.val) hi
    rw [Function.update_of_ne hi]
    by_cases h29 : i.val<29
    · simp only [stageStore,dif_pos h29,PartnerRunner.state,Fin.val_mk,if_neg h]
    · simp only [stageStore,dif_neg h29]

/-- The actual machine conditionally enters mixing only after a success-prefixed
initializer witness. A failed initializer returns the empty marker unchanged. -/
theorem program_executes {extra n : ℕ} (B : OracleBlock (extra+29)) (p : Polynomial ℕ) (init : Initializer)
    (hB : InitializerSpec B p init) (g : BitString → ℕ) (G : MatrixGraph n) (N : ℕ) (hn : n≤N)
    (initTape chainTape : BitString) (htape : initTape.length≤3*N^4) :
    ∃s : Store (extra+29),∃cost,(program B).Executes g
      (stageStore (PartnerRunner.state G.bits n N chainTape [] [] []) initTape) s cost ∧
      s 2=PartnerRunner.afterInitialize G N (init G N initTape) chainTape ∧ cost≤(time p).eval N := by
  obtain ⟨a,ha,hba⟩ := hB.executes g G N hn initTape chainTape htape
  cases hi : init G N initTape with
  | none =>
    simp only [hi,initialCode] at ha
    have hb := branchPop_empty (2:Fin (extra+30)) skip (clear 2) (mix extra) g
      (s:=stageStore (PartnerRunner.state G.bits n N chainTape [] [] []) []) rfl
      (skip_executes g _)
    refine ⟨_,a+3+2,seq_executes _ _ g ha hb,?_,?_⟩
    · simp [hi,PartnerRunner.afterInitialize,stageStore,PartnerRunner.state,Nat.mod_eq_of_lt (show 2<extra+29+1 by omega)]
    · simp only [time,Polynomial.eval_add,Polynomial.eval_ofNat]
      omega
  | some P =>
    simp only [hi,initialCode] at ha
    obtain ⟨b,hb,hbb⟩ := mix_executes (extra:=extra) g G N hn P chainTape
    have hh := branchPop_true (2:Fin (extra+30)) skip (clear 2) (mix extra) g
      (s:=stageStore (PartnerRunner.state G.bits n N chainTape (PartnerOutput.success G P) [] []) [])
      (rest:=PartnerOutput.witness G P) rfl (by rw [pop_success];exact hb)
    refine ⟨_,a+(b+2)+2,seq_executes _ _ g ha hh,?_,?_⟩
    · simp [hi,PartnerRunner.afterInitialize,stageStore,PartnerRunner.state,Nat.mod_eq_of_lt (show 2<extra+29+1 by omega)]
    · simp only [time,Polynomial.eval_add,Polynomial.eval_ofNat]
      omega

lemma program_queryFree {extra : ℕ} (B : OracleBlock (extra+29)) (p : Polynomial ℕ) (init : Initializer)
    (hB : InitializerSpec B p init) : (program B).QueryFree := seq_queryFree _ _ hB.queryFree
  (branchPop_queryFree _ _ _ _ skip_queryFree (clear_queryFree _) (PartnerRunner.on_queryFree _))

end HiddenCircuits.Approximation.SamplerRuntime.PartnerInitialized
