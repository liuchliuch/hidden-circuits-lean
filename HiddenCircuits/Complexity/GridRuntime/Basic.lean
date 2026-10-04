import HiddenCircuits.Complexity.OracleLibrary
import HiddenCircuits.Complexity.OracleBlockNoQuery

/-! Metadata and literal counter instructions for a finite rectangular-grid iterator. -/
namespace HiddenCircuits.Complexity.GridRuntime
open OracleBlock

abbrev Frame (k : ℕ) := Fin k → BitString

def port {k : ℕ} (i : Fin 9) : Fin ((k+8)+1) := ⟨i.val,by omega⟩

def store {k : ℕ} (n m i j : ℕ) (inner outer : BitString) (d : Frame k) : Store (k+8) := fun r =>
  if r.val=0 then List.replicate n true else if r.val=1 then List.replicate m true
  else if r.val=2 then List.replicate i true else if r.val=3 then List.replicate (n-i) true
  else if r.val=4 then List.replicate j true else if r.val=5 then List.replicate (m-j) true
  else if r.val=6 then inner else if r.val=7 then outer
  else if h:9≤r.val then d ⟨r.val-9,by have := r.isLt;omega⟩ else []

def dataEmbedding (k : ℕ) : Fin k ↪ Fin ((k+8)+1) where
  toFun i := ⟨i.val+9,by omega⟩
  inj' := by intro i j h;apply Fin.ext;have hh := congrArg (fun z : Fin ((k+8)+1) => z.val) h;change i.val+9=j.val+9 at hh;omega

@[simp] theorem store_data {k : ℕ} (n m i j : ℕ) (inner outer : BitString) (d : Frame k) (r : Fin k) :
    store n m i j inner outer d (dataEmbedding k r)=d r := by
  simp [store,dataEmbedding]

/-- Increment an index and physically remove one bit from its truncated complement. -/
def advance {k : ℕ} (index complement : Fin (k+1)) : OracleBlock k where
  labelCount := 3
  start := 0
  exit := 2
  code q := if q=0 then .push index true 1 else if q=1 then .pop complement 2 2 2 else .halt
  exit_halt := rfl

theorem advance_executes {k : ℕ} (g : BitString → ℕ) (index complement : Fin (k+1))
    (hne : index≠complement) (s : Store k) :
    (advance index complement).Executes g s
      (Function.update (Function.update s index (true::s index)) complement (s complement).tail) 2 := by
  let t := Function.update s index (true::s index)
  have h₁ : (advance index complement).machine.step g ((advance index complement).config (0:Fin 3) s)=
      some ((advance index complement).config (1:Fin 3) t,1) := by
    simp [OracleMachine.step,machine,advance,config,t]
  have h₂ : (advance index complement).machine.step g ((advance index complement).config (1:Fin 3) t)=
      some ((advance index complement).config (2:Fin 3)
        (Function.update t complement (s complement).tail),1) := by
    simp only [OracleMachine.step,machine,advance,config,Fin.isValue,Fin.zero_eta,Fin.mk_one,
      show (1:Fin 3)≠0 by decide,ite_false,ite_true]
    have ht : t complement=s complement := Function.update_of_ne hne.symm _ _
    rw [ht]
    cases hs:s complement with
    | nil =>
      have he : t complement=[] := ht.trans hs
      simp only [List.tail_nil]
      rw [←he,Function.update_eq_self]
    | cons b bs => cases b <;> rfl
  exact (OracleMachine.Steps.single h₁).trans (OracleMachine.Steps.single h₂)

theorem advance_queryFree {k : ℕ} (index complement : Fin (k+1)) : (advance index complement).QueryFree := by
  intro q a b next
  fin_cases q <;> simp [machine,advance]

 theorem store_advance_column {k : ℕ} (n m i j : ℕ) (inner outer : BitString) (d : Frame k) :
    Function.update (Function.update (store n m i j inner outer d) (port (k:=k) 4)
      (true::store n m i j inner outer d (port (k:=k) 4))) (port 5) (store n m i j inner outer d (port (k:=k) 5)).tail=
      store n m i (j+1) inner outer d := by
  funext r
  by_cases h:r.val<9
  · interval_cases hr:r.val <;> simp [port,store,Function.update_apply,Fin.ext_iff,hr,List.replicate_succ,List.tail_replicate,Nat.sub_sub]
  · have h9:9≤r.val := by omega
    simp [port,store,Function.update_apply,Fin.ext_iff,show r.val≠0 by omega,show r.val≠1 by omega,
      show r.val≠2 by omega,show r.val≠3 by omega,show r.val≠4 by omega,show r.val≠5 by omega,
      show r.val≠6 by omega,show r.val≠7 by omega]

 theorem store_advance_row {k : ℕ} (n m i j : ℕ) (inner outer : BitString) (d : Frame k) :
    Function.update (Function.update (store n m i j inner outer d) (port (k:=k) 2)
      (true::store n m i j inner outer d (port (k:=k) 2))) (port 3) (store n m i j inner outer d (port (k:=k) 3)).tail=
      store n m (i+1) j inner outer d := by
  funext r
  by_cases h:r.val<9
  · interval_cases hr:r.val <;> simp [port,store,Function.update_apply,Fin.ext_iff,hr,List.replicate_succ,List.tail_replicate,Nat.sub_sub]
  · simp [port,store,Function.update_apply,Fin.ext_iff,show r.val≠0 by omega,show r.val≠1 by omega,
      show r.val≠2 by omega,show r.val≠3 by omega,show r.val≠4 by omega,show r.val≠5 by omega,
      show r.val≠6 by omega,show r.val≠7 by omega]

 theorem store_update_inner {k : ℕ} (n m i j : ℕ) (inner outer rest : BitString) (d : Frame k) :
    Function.update (store n m i j inner outer d) (port (k:=k) 6) rest=store n m i j rest outer d := by
  funext r
  by_cases h:r.val<9
  · interval_cases hr:r.val <;> simp [port,store,Function.update_apply,Fin.ext_iff,hr]
  · simp [port,Function.update_apply,Fin.ext_iff,show r.val≠6 by omega,store,show r.val≠0 by omega,show r.val≠1 by omega,show r.val≠2 by omega,show r.val≠3 by omega,show r.val≠4 by omega,show r.val≠5 by omega]

 theorem store_update_outer {k : ℕ} (n m i j : ℕ) (inner outer rest : BitString) (d : Frame k) :
    Function.update (store n m i j inner outer d) (port (k:=k) 7) rest=store n m i j inner rest d := by
  funext r
  by_cases h:r.val<9
  · interval_cases hr:r.val <;> simp [port,store,Function.update_apply,Fin.ext_iff,hr]
  · simp [port,Function.update_apply,Fin.ext_iff,show r.val≠7 by omega,store,show r.val≠0 by omega,show r.val≠1 by omega,show r.val≠2 by omega,show r.val≠3 by omega,show r.val≠4 by omega,show r.val≠5 by omega,show r.val≠6 by omega]

end HiddenCircuits.Complexity.GridRuntime
