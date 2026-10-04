import HiddenCircuits.GraphReduction.Runtime.PairEval.WordNaturalOutput
import HiddenCircuits.Complexity.EvalEncodingSoundness

/-! A finite malformed-zero guard around the concrete canonical signed WordEval solver.
The final raw-input theorem instantiates the validation contract with its actual
query-free parser; the contract itself is not an input certificate. -/
namespace HiddenCircuits.GraphReduction.Runtime.PairEval.WordRawGuard
open Complexity OracleBlock Polynomial
open Circuit.Runtime
set_option maxHeartbeats 1000000

def marker (xs : BitString) : BitString := if (decodeWord xs).isSome then [true] else []
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
noncomputable def solver : OracleBlock 128 := rename WordNaturalOutput.program solverEmbedding
noncomputable def select : OracleBlock 128 := branchPop 1 (clear 0) (clear 0) solver
noncomputable def program (V : OracleBlock 31) : OracleBlock 128 :=
  seq (rename V validationEmbedding) select
noncomputable def time (P : Polynomial ℕ) : Polynomial ℕ := P+WordNaturalOutput.time+X+5

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

lemma solver_executes (g : BitString→ℕ) (w : WordInstance) (hg : WordCell.oracleSpec g) :
    ∃c,solver.Executes g (Function.update (fun _=>[]) 0 (wordBits w))
      (Function.update (fun _=>[]) 0 (Computability.encodeNat (WordEvalOracle.signedCode w.value.num))) c ∧ c≤WordNaturalOutput.time.eval (wordBits w).length := by
  obtain ⟨c,hc,hb⟩ := WordNaturalOutput.program_executes g hg w
  refine ⟨c,?_,hb⟩
  apply rename_executes_to WordNaturalOutput.program solverEmbedding g hc
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

theorem select_executes (g : BitString→ℕ) (hg : WordCell.oracleSpec g) (xs : BitString) :
    ∃c,select.Executes g (validationStore xs)
      (Function.update (fun _=>[]) 0 (Computability.encodeNat (WordEvalOracle.problem xs))) c ∧
      c≤WordNaturalOutput.time.eval xs.length+xs.length+3 := by
  cases hd : decodeWord xs with
  | none =>
    have he : (validationStore xs : Store 128)=Function.update (fun _=>[]) 0 xs := by
      funext i;simp [validationStore,marker,hd,Function.update_apply]
    have hc : (clear (0:Fin 129)).Executes g (validationStore xs) (Function.update (fun _=>[]) 0 []) (xs.length+1) := by
      rw [he]
      simpa only [Function.update_self,Function.update_idem] using clear_executes g (0:Fin 129) (Function.update (fun _=>[]) 0 xs)
    have hs : (validationStore xs : Store 128) 1=[] := by simp [validationStore,marker,hd]
    refine ⟨xs.length+1+2,?_,by omega⟩
    simpa only [WordEvalOracle.problem,hd,Computability.encodeNat] using branchPop_empty (1:Fin 129) (clear 0) (clear 0) solver g hs hc
  | some w =>
    have he : wordBits w=xs := wordBits_of_decodeWord hd
    obtain ⟨c,hc,hb⟩ := solver_executes g w hg
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
    simpa only [WordEvalOracle.problem,hd] using branchPop_true (1:Fin 129) (clear 0) (clear 0) solver g hs hc

theorem program_executes (V : OracleBlock 31) (P : Polynomial ℕ) (hV : ValidatorSpec V P)
    (g : BitString→ℕ) (hg : WordCell.oracleSpec g) (xs : BitString) :
    ∃c,(program V).Executes g (Function.update (fun _=>[]) 0 xs)
      (Function.update (fun _=>[]) 0 (Computability.encodeNat (WordEvalOracle.problem xs))) c ∧ c≤(time P).eval xs.length := by
  obtain ⟨a,ha,hab⟩ := validation_executes V P hV g xs
  obtain ⟨b,hb,hbb⟩ := select_executes g hg xs
  refine ⟨_,seq_executes _ _ g ha hb,?_⟩
  simp only [time,eval_add,eval_X,eval_ofNat]
  omega

theorem reduction (V : OracleBlock 31) (P : Polynomial ℕ) (hV : ValidatorSpec V P)
    (g : BitString→ℕ) (hg : WordCell.oracleSpec g) : PolyTuringReduction WordEvalOracle.problem g := by
  refine ⟨(program V).machine,time P,?_⟩
  intro xs
  obtain ⟨c,hc,hb⟩ := program_executes V P hV g hg xs
  refine ⟨(program V).config (program V).exit (Function.update (fun _=>[]) 0 (Computability.encodeNat (WordEvalOracle.problem xs))),c,?_,rfl,hb⟩
  apply (OracleMachine.runs_iff_steps_halt _).mpr
  exact ⟨hc,by simp [OracleMachine.step,OracleBlock.config,OracleBlock.machine,(program V).exit_halt]⟩
end HiddenCircuits.GraphReduction.Runtime.PairEval.WordRawGuard
