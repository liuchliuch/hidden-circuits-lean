import HiddenCircuits.Complexity.GraphVerifier.MatchingRowMachine
import HiddenCircuits.Complexity.GraphVerifier.MatchingRuntimeSemantics
import Mathlib.Data.Fintype.Fin

/-! Counted repeated exactly-one row scanning of the real matching matrix certificate. -/
namespace HiddenCircuits.Complexity.GraphVerifier.MatchingRuntime
open OracleBlock

def oneRowEmbedding : Fin 3 ↪ Fin 6 where
  toFun i := ⟨i.val+1,by omega⟩
  inj' := by intro i j h;apply Fin.ext;have := congrArg (fun z : Fin 6 => z.val) h;simp at this;omega
noncomputable def oneRowsBody : OracleBlock 5 :=
  seq (copyOn 0 1 5 (by decide) (by decide) (by decide)) (rename oneRowBlock oneRowEmbedding)
noncomputable def oneRowsLoop : OracleBlock 5 := whilePop 4 oneRowsBody oneRowsBody
noncomputable def oneRowsBlock : OracleBlock 5 :=
  seq (copyOn 0 4 5 (by decide) (by decide) (by decide)) oneRowsLoop

def oneRowsStore (n : ℕ) (inner data flag outer : BitString) : Store 5 := fun r =>
  if r.val=0 then List.replicate n true else if r.val=1 then inner else if r.val=2 then data
  else if r.val=3 then flag else if r.val=4 then outer else []

def rowFlag (n : ℕ) (data : BitString) (i : ℕ) : Bool :=
  decide (((data.drop (n*i)).take n).count true=1)
def allRowsValue (n : ℕ) (data : BitString) : ℕ → ℕ → Bool → Bool
  | _,0,a => a
  | i,m+1,a => allRowsValue n data (i+1) m (a && rowFlag n data i)

 theorem oneRowsBody_executes (g : BitString → ℕ) (n i : ℕ) (data outer : BitString) (a : Bool)
    (hi : n*(i+1)≤data.length) :
    oneRowsBody.Executes g (oneRowsStore n [] (data.drop (n*i)) [a] outer)
      (oneRowsStore n [] (data.drop (n*(i+1))) [a && rowFlag n data i] outer) (7*n+7) := by
  let s₀ := oneRowsStore n [] (data.drop (n*i)) [a] outer
  let s₁ := oneRowsStore n (List.replicate n true) (data.drop (n*i)) [a] outer
  let s₂ := oneRowsStore n [] (data.drop (n*(i+1))) [a && rowFlag n data i] outer
  have h₁ : (copyOn (0:Fin 6) 1 5 (by decide) (by decide) (by decide)).Executes g s₀ s₁ (5*n+2) := by
    convert copyOn_executes g (0:Fin 6) 1 5 (by decide) (by decide) (by decide) s₀ rfl using 1
    · funext r;fin_cases r <;> simp [s₀,s₁,oneRowsStore]
    · simp [s₀,oneRowsStore]
  have hc := oneRow_executes g (List.replicate n true) (data.drop (n*i)) a
    (by simp only [List.length_replicate,List.length_drop];rw [Nat.mul_add,Nat.mul_one] at hi;omega)
  have h₂ : (rename oneRowBlock oneRowEmbedding).Executes g s₁ s₂ (2*n+3) := by
    apply rename_executes_to oneRowBlock oneRowEmbedding g (by simpa using hc)
    · funext r;fin_cases r <;> rfl
    · funext r;fin_cases r <;> simp [s₂,oneRowsStore,rowMachineStore,oneRowEmbedding,rowFlag,List.drop_drop,Nat.mul_add,Nat.add_comm]
    · intro r hr;fin_cases r <;> first | rfl | exact False.elim (hr 0 rfl) | exact False.elim (hr 1 rfl) | exact False.elim (hr 2 rfl)
  convert seq_executes _ _ g h₁ h₂ using 1 <;> omega

 theorem oneRows_loop (g : BitString → ℕ) (n i m : ℕ) (data : BitString) (a : Bool)
    (hi : n*(i+m)≤data.length) :
    WhileExecution (4:Fin 6) oneRowsBody oneRowsBody g
      (oneRowsStore n [] (data.drop (n*i)) [a] (List.replicate m true))
      (oneRowsStore n [] (data.drop (n*(i+m))) [allRowsValue n data i m a] []) (m*(7*n+9)+1) := by
  induction m generalizing i a with
  | zero =>
    simpa [allRowsValue] using (WhileExecution.empty
      (stack := (4:Fin 6)) (B := oneRowsBody) (C := oneRowsBody) (g := g)
      (oneRowsStore n [] (data.drop (n*i)) [a] []) rfl)
  | succ m ih =>
    have hstep := oneRowsBody_executes g n i data (List.replicate m true) a (by nlinarith)
    have htail := ih (i+1) (a && rowFlag n data i) (by nlinarith)
    have he : Function.update (oneRowsStore n [] (data.drop (n*i)) [a] (List.replicate (m+1) true)) (4:Fin 6)
        (List.replicate m true)=oneRowsStore n [] (data.drop (n*i)) [a] (List.replicate m true) := by
      funext r;fin_cases r <;> rfl
    have hh := WhileExecution.one
      (stack := (4:Fin 6)) (B := oneRowsBody) (C := oneRowsBody) (g := g)
      (show oneRowsStore n [] (data.drop (n*i)) [a] (List.replicate (m+1) true) 4=true::List.replicate m true from rfl)
      (by rw [he];exact hstep) htail
    convert hh using 1 <;> simp [allRowsValue,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] <;> ring

 theorem oneRows_executes (g : BitString → ℕ) (n : ℕ) (data : BitString) (a : Bool)
    (hi : n*n≤data.length) :
    oneRowsBlock.Executes g (oneRowsStore n [] data [a] [])
      (oneRowsStore n [] (data.drop (n*n)) [allRowsValue n data 0 n a] []) (7*n*n+14*n+5) := by
  have h₁ : (copyOn (0:Fin 6) 4 5 (by decide) (by decide) (by decide)).Executes g
      (oneRowsStore n [] data [a] []) (oneRowsStore n [] data [a] (List.replicate n true)) (5*n+2) := by
    convert copyOn_executes g (0:Fin 6) 4 5 (by decide) (by decide) (by decide) (oneRowsStore n [] data [a] []) rfl using 1
    · funext r;fin_cases r <;> simp [oneRowsStore]
    · simp [oneRowsStore]
  have h₂ := whilePop_executes _ _ _ g (oneRows_loop g n 0 n data a (by simpa using hi))
  have hh := seq_executes _ _ g h₁ (by simpa using h₂)
  convert hh using 1 <;> ring

 theorem allRowsValue_all (n : ℕ) (data : BitString) (i m : ℕ) (a : Bool) :
    allRowsValue n data i m a=(a && (List.range' i m).all (rowFlag n data)) := by
  induction m generalizing i a with
  | zero => simp [allRowsValue]
  | succ m ih => simp [allRowsValue,List.range'_succ,ih,Bool.and_assoc]

 theorem oneRows_queryFree : oneRowsBlock.QueryFree := by
  have hb : oneRowsBody.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (rename_queryFree _ _ oneRow_queryFree)
  exact seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (whilePop_queryFree _ _ _ hb hb)

end HiddenCircuits.Complexity.GraphVerifier.MatchingRuntime
