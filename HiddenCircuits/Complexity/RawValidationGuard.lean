import HiddenCircuits.Complexity.OracleMove

/-! A reusable physical malformed-zero guard. The helper's encoding and solver
contracts are discharged by concrete native circuit programs at each endpoint. -/
namespace HiddenCircuits.Complexity.RawValidationGuard
open OracleBlock Polynomial
set_option maxHeartbeats 1000000
structure InputProblem where
  Input : Type
  encode : Input→BitString
  decode : BitString→Option Input
  value : Input→ℕ
  decode_sound : ∀{xs w},decode xs=some w→encode w=xs
noncomputable def InputProblem.total (F : InputProblem) (xs : BitString) : ℕ :=
  match F.decode xs with | none=>0 | some w=>F.value w
variable {k : ℕ}

def marker (F : InputProblem) (xs : BitString) : BitString := if (F.decode xs).isSome then [true] else []
def validationStore {k : ℕ} (F : InputProblem) (xs : BitString) : Store (k+1) := fun i=>
  if i.val=0 then xs else if i.val=1 then marker F xs else []
def ValidatorSpec (F : InputProblem) (V : OracleBlock 31) (P : Polynomial ℕ) : Prop :=
  ∀g xs,∃c,V.Executes g (Function.update (fun _=>[]) 0 xs) (validationStore F xs) c ∧ c≤P.eval xs.length

def validationEmbedding : Fin 32 ↪ Fin (k+32) where
  toFun i:=⟨i.val,by omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun z : Fin (k+32)=>z.val) h)
def solverPort (i : ℕ) : ℕ := if i=0 then 0 else i+31
lemma solverPort_injective : Function.Injective solverPort := by
  intro i j h
  unfold solverPort at h
  split_ifs at h <;> omega
def solverEmbedding : Fin (k+1) ↪ Fin (k+32) where
  toFun i := ⟨solverPort i.val,by unfold solverPort;split_ifs <;> omega⟩
  inj' := by intro i j h;apply Fin.ext;exact solverPort_injective (congrArg Fin.val h)
noncomputable def solver (S : OracleBlock k) : OracleBlock (k+31) := rename S solverEmbedding
noncomputable def select (S : OracleBlock k) : OracleBlock (k+31) := branchPop 1 (clear 0) (clear 0) (solver S)
noncomputable def program (V : OracleBlock 31) (S : OracleBlock k) : OracleBlock (k+31) :=
  seq (rename V validationEmbedding) (select S)
noncomputable def time (P Q : Polynomial ℕ) : Polynomial ℕ := P+Q+X+5

lemma validation_executes (F : InputProblem) (k : ℕ) (V : OracleBlock 31) (P : Polynomial ℕ) (hV : ValidatorSpec F V P) (g : BitString→ℕ) (xs : BitString) :
    ∃c,(rename V (validationEmbedding (k:=k))).Executes g (Function.update (fun _=>[]) 0 xs) (validationStore F xs) c ∧ c≤P.eval xs.length := by
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

def SolverSpec (F : InputProblem) (S : OracleBlock k) (Q : Polynomial ℕ) (g : BitString→ℕ) : Prop :=
  ∀w : F.Input,∃c,S.Executes g (Function.update (fun _=>[]) 0 (F.encode w))
    (Function.update (fun _=>[]) 0 (Computability.encodeNat (F.value w))) c ∧ c≤Q.eval (F.encode w).length

lemma solver_executes (F : InputProblem) (S : OracleBlock k) (Q : Polynomial ℕ)
    (g : BitString→ℕ) (hS : SolverSpec F S Q g) (w : F.Input) :
    ∃c,(solver S).Executes g (Function.update (fun _=>[]) 0 (F.encode w))
      (Function.update (fun _=>[]) 0 (Computability.encodeNat (F.value w))) c ∧ c≤Q.eval (F.encode w).length := by
  obtain ⟨c,hc,hb⟩ := hS w
  refine ⟨c,?_,hb⟩
  apply rename_executes_to S solverEmbedding g hc
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

theorem select_executes (F : InputProblem) (S : OracleBlock k) (Q : Polynomial ℕ)
    (g : BitString→ℕ) (hS : SolverSpec F S Q g) (xs : BitString) :
    ∃c,(select S).Executes g (validationStore F xs)
      (Function.update (fun _=>[]) 0 (Computability.encodeNat (F.total xs))) c ∧
      c≤Q.eval xs.length+xs.length+3 := by
  cases hd : F.decode xs with
  | none =>
    have he : (validationStore F xs : Store (k+31))=Function.update (fun _=>[]) 0 xs := by
      funext i;simp [validationStore,marker,hd,Function.update_apply]
    have hc : (clear (0:Fin (k+32))).Executes g (validationStore F xs) (Function.update (fun _=>[]) 0 []) (xs.length+1) := by
      rw [he]
      simpa only [Function.update_self,Function.update_idem] using clear_executes g (0:Fin (k+32)) (Function.update (fun _=>[]) 0 xs)
    have hs : (validationStore F xs : Store (k+31)) 1=[] := by simp [validationStore,marker,hd]
    refine ⟨xs.length+1+2,?_,by omega⟩
    simpa only [InputProblem.total,hd,Computability.encodeNat] using branchPop_empty (1:Fin (k+32)) (clear 0) (clear 0) (solver S) g hs hc
  | some w =>
    have he : F.encode w=xs := F.decode_sound hd
    obtain ⟨c,hc,hb⟩ := solver_executes F S Q g hS w
    rw [he] at hc hb
    have hs : (validationStore F xs : Store (k+31)) 1=true::[] := by simp [validationStore,marker,hd]
    have hstate : Function.update (validationStore F xs : Store (k+31)) 1 []=Function.update (fun _=>[]) 0 xs := by
      funext i
      by_cases h1:i=1
      · subst i;rfl
      · have hv1:i.val≠1:=fun h=>h1 (Fin.ext h)
        simp [Function.update_of_ne h1,validationStore,hv1,Function.update_apply]
    rw [←hstate] at hc
    refine ⟨c+2,?_,by omega⟩
    simpa only [InputProblem.total,hd] using branchPop_true (1:Fin (k+32)) (clear 0) (clear 0) (solver S) g hs hc

theorem program_executes (F : InputProblem) (V : OracleBlock 31) (S : OracleBlock k)
    (P Q : Polynomial ℕ) (hV : ValidatorSpec F V P) (g : BitString→ℕ) (hS : SolverSpec F S Q g) (xs : BitString) :
    ∃c,(program V S).Executes g (Function.update (fun _=>[]) 0 xs)
      (Function.update (fun _=>[]) 0 (Computability.encodeNat (F.total xs))) c ∧ c≤(time P Q).eval xs.length := by
  obtain ⟨a,ha,hab⟩ := validation_executes F k V P hV g xs
  obtain ⟨b,hb,hbb⟩ := select_executes F S Q g hS xs
  refine ⟨_,seq_executes _ _ g ha hb,?_⟩
  simp only [time,eval_add,eval_X,eval_ofNat]
  omega

theorem reduction (F : InputProblem) (V : OracleBlock 31) (S : OracleBlock k)
    (P Q : Polynomial ℕ) (hV : ValidatorSpec F V P) (g : BitString→ℕ) (hS : SolverSpec F S Q g) : PolyTuringReduction F.total g := by
  refine ⟨(program V S).machine,time P Q,?_⟩
  intro xs
  obtain ⟨c,hc,hb⟩ := program_executes F V S P Q hV g hS xs
  refine ⟨(program V S).config (program V S).exit (Function.update (fun _=>[]) 0 (Computability.encodeNat (F.total xs))),c,?_,rfl,hb⟩
  apply (OracleMachine.runs_iff_steps_halt _).mpr
  exact ⟨hc,by simp [OracleMachine.step,OracleBlock.config,OracleBlock.machine,(program V S).exit_halt]⟩
end HiddenCircuits.Complexity.RawValidationGuard
