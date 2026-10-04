import HiddenCircuits.GraphReduction.Runtime.PairEval.GraphSolver
import HiddenCircuits.Complexity.EvalEncodingSoundness

/-! A finite malformed-zero guard around the concrete canonical PairEval solver.
The final raw-input theorem instantiates the validation contract with its actual
query-free parser; the contract itself is not an input certificate. -/
namespace HiddenCircuits.GraphReduction.Runtime.PairEval.RawGuard
open Complexity OracleBlock Polynomial
set_option maxHeartbeats 1000000

def marker (xs : BitString) : BitString := if (decodePairInput xs).isSome then [true] else []
def validationStore {k : ℕ} (xs : BitString) : Store (k+1) := fun i=>
  if i.val=0 then xs else if i.val=1 then marker xs else []
def ValidatorSpec (V : OracleBlock 31) (P : Polynomial ℕ) : Prop :=
  ∀g xs,∃c,V.Executes g (Function.update (fun _=>[]) 0 xs) (validationStore xs) c ∧ c≤P.eval xs.length

def validationEmbedding : Fin 32 ↪ Fin 129 := Fin.castAddEmb 97
def solverPort (i : ℕ) : ℕ := if i=0 then 0 else i+31
lemma solverPort_injective : Function.Injective solverPort := by
  intro i j h
  unfold solverPort at h
  split_ifs at h <;> omega
def solverEmbedding : Fin 98 ↪ Fin 129 where
  toFun i := ⟨solverPort i.val,by unfold solverPort;split_ifs <;> omega⟩
  inj' := by intro i j h;apply Fin.ext;exact solverPort_injective (congrArg Fin.val h)
noncomputable def solver (kind : Driver.Target) : OracleBlock 128 := rename (GraphSolver.program kind) solverEmbedding
noncomputable def select (kind : Driver.Target) : OracleBlock 128 := branchPop 1 (clear 0) (clear 0) (solver kind)
noncomputable def program (V : OracleBlock 31) (kind : Driver.Target) : OracleBlock 128 :=
  seq (rename V validationEmbedding) (select kind)
noncomputable def time (P : Polynomial ℕ) (kind : Driver.Target) : Polynomial ℕ := P+GraphSolver.time kind+X+5

lemma validation_executes (V : OracleBlock 31) (P : Polynomial ℕ) (hV : ValidatorSpec V P) (g : BitString→ℕ) (xs : BitString) :
    ∃c,(rename V validationEmbedding).Executes g (Function.update (fun _=>[]) 0 xs) (validationStore xs) c ∧ c≤P.eval xs.length := by
  obtain ⟨c,hc,hb⟩ := hV g xs
  refine ⟨c,?_,hb⟩
  apply rename_executes_to V validationEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;rfl
  · intro i hi
    have h0 : i≠0 := fun h=>hi 0 h.symm
    have hv0 : i.val≠0 := fun h=>h0 (Fin.ext h)
    have hv1 : i.val≠1 := fun h=>hi 1 (Fin.ext h.symm)
    simp [validationStore,Function.update_of_ne h0,hv0,hv1]

lemma solver_executes (kind : Driver.Target) (g : BitString→ℕ) (w : PairInput) (hg : Driver.CorrectOracle kind g w) :
    ∃c,(solver kind).Executes g (Function.update (fun _=>[]) 0 (pairInputBits w))
      (Function.update (fun _=>[]) 0 (Computability.encodeNat w.value)) c ∧ c≤(GraphSolver.time kind).eval (pairInputBits w).length := by
  obtain ⟨c,hc,hb⟩ := GraphSolver.program_executes kind g w hg
  simp only [pairEval_pairInputBits] at hc
  refine ⟨c,?_,hb⟩
  apply rename_executes_to (GraphSolver.program kind) solverEmbedding g hc
  · funext i;by_cases h:i.val=0
    · have hi:i=0:=Fin.ext h;subst i;rfl
    · have hi:i≠0:=by intro hh;subst i;contradiction
      simp [Function.comp_def,solverEmbedding,solverPort,h,hi,Function.update_of_ne hi,Function.update_apply]
  · funext i;by_cases h:i.val=0
    · have hi:i=0:=Fin.ext h;subst i;rfl
    · have hi:i≠0:=by intro hh;subst i;contradiction
      simp [Function.comp_def,solverEmbedding,solverPort,h,hi,Function.update_of_ne hi,Function.update_apply]
  · intro i hi
    have h0:i≠0:=fun h=>hi 0 h.symm
    simp only [Function.update_of_ne h0]

theorem select_executes (kind : Driver.Target) (g : BitString→ℕ) (hg : ∀w,Driver.CorrectOracle kind g w) (xs : BitString) :
    ∃c,(select kind).Executes g (validationStore xs)
      (Function.update (fun _=>[]) 0 (Computability.encodeNat (pairEval xs))) c ∧
      c≤(GraphSolver.time kind).eval xs.length+xs.length+3 := by
  cases hd : decodePairInput xs with
  | none =>
    have he : (validationStore xs : Store 128)=Function.update (fun _=>[]) 0 xs := by
      funext i;simp [validationStore,marker,hd,Function.update_apply]
    have hc : (clear (0:Fin 129)).Executes g (validationStore xs) (Function.update (fun _=>[]) 0 []) (xs.length+1) := by
      rw [he]
      simpa only [Function.update_self,Function.update_idem] using clear_executes g (0:Fin 129) (Function.update (fun _=>[]) 0 xs)
    have hs : (validationStore xs : Store 128) 1=[] := by simp [validationStore,marker,hd]
    refine ⟨xs.length+1+2,?_,by omega⟩
    simpa only [pairEval_malformed xs hd,Computability.encodeNat] using branchPop_empty (1:Fin 129) (clear 0) (clear 0) (solver kind) g hs hc
  | some w =>
    have he : pairInputBits w=xs := pairInputBits_of_decodePairInput hd
    obtain ⟨c,hc,hb⟩ := solver_executes kind g w (hg w)
    rw [he] at hc hb
    have hs : (validationStore xs : Store 128) 1=true::[] := by simp [validationStore,marker,hd]
    have hstate : Function.update (validationStore xs : Store 128) 1 []=Function.update (fun _=>[]) 0 xs := by
      funext i
      by_cases h1:i=1
      · subst i;rfl
      · have hv1:i.val≠1:=fun h=>h1 (Fin.ext h)
        simp [Function.update_of_ne h1,validationStore,hv1,Function.update_apply]
    rw [←hstate] at hc
    refine ⟨c+2,?_,by omega⟩
    simpa only [pairEval,hd] using branchPop_true (1:Fin 129) (clear 0) (clear 0) (solver kind) g hs hc

theorem program_executes (V : OracleBlock 31) (P : Polynomial ℕ) (hV : ValidatorSpec V P)
    (kind : Driver.Target) (g : BitString→ℕ) (hg : ∀w,Driver.CorrectOracle kind g w) (xs : BitString) :
    ∃c,(program V kind).Executes g (Function.update (fun _=>[]) 0 xs)
      (Function.update (fun _=>[]) 0 (Computability.encodeNat (pairEval xs))) c ∧ c≤(time P kind).eval xs.length := by
  obtain ⟨a,ha,hab⟩ := validation_executes V P hV g xs
  obtain ⟨b,hb,hbb⟩ := select_executes kind g hg xs
  refine ⟨_,seq_executes _ _ g ha hb,?_⟩
  simp only [time,eval_add,eval_X,eval_ofNat]
  omega

theorem reduction (V : OracleBlock 31) (P : Polynomial ℕ) (hV : ValidatorSpec V P)
    (kind : Driver.Target) (g : BitString→ℕ) (hg : ∀w,Driver.CorrectOracle kind g w) : PolyTuringReduction pairEval g := by
  refine ⟨(program V kind).machine,time P kind,?_⟩
  intro xs
  obtain ⟨c,hc,hb⟩ := program_executes V P hV kind g hg xs
  refine ⟨(program V kind).config (program V kind).exit (Function.update (fun _=>[]) 0 (Computability.encodeNat (pairEval xs))),c,?_,rfl,hb⟩
  apply (OracleMachine.runs_iff_steps_halt _).mpr
  exact ⟨hc,by simp [OracleMachine.step,OracleBlock.config,OracleBlock.machine,(program V kind).exit_halt]⟩
end HiddenCircuits.GraphReduction.Runtime.PairEval.RawGuard
