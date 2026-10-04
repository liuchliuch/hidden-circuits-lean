import HiddenCircuits.Complexity.MatrixEmitterSerialization
import HiddenCircuits.Approximation.SelfReduction.Runtime.WordEmit

/-! Fresh reconstruction: actual word-valued framed row-major matrix emission. -/
namespace HiddenCircuits.Approximation.Initialization.WordMatrixEmitter
open Complexity OracleBlock MatrixEmitter
open HiddenCircuits.Approximation.SelfReduction.Runtime
variable {k : ℕ}

lemma store_value (n i j : ℕ) (value out inner outer next : BitString) (params : Store (k+7)) :
    Function.update (store n i j value out inner outer params) (port 3) next=
      store n i j next out inner outer params := by
  funext r;simp [store,Function.update_apply];split_ifs <;> simp_all [port]
noncomputable def emitWord : OracleBlock (k+7) := emitWordReversed (port 3) (port 4)
lemma emitWord_executes (g : BitString → ℕ) (n i j : ℕ) (word out inner outer : BitString)
    (params : Store (k+7)) :
    emitWord.Executes g (store n i j word out inner outer params)
      (store n i j [] ((true::pairBits word []).reverse++out) inner outer params) (6*word.length+7) := by
  simpa only [emitWord,store_core,Matrix.cons_val_zero,Matrix.cons_val_succ,store_value,store_output] using
    emitWordReversed_executes g (port (k:=k) 3) (port 4) (by simp [port])
      (store n i j word out inner outer params)
noncomputable def entryBody (B : OracleBlock (k+7)) : OracleBlock (k+7) :=
  seq B (seq emitWord (push (port 2) true))
noncomputable def rowLoop (B : OracleBlock (k+7)) : OracleBlock (k+7) :=
  whilePop (port 5) (entryBody B) (entryBody B)

def rowOutput (entry : ℕ → ℕ → BitString) (i : ℕ) : ℕ → ℕ → BitString → BitString
  | _,0,out => out
  | j,m+1,out => rowOutput entry i (j+1) m ((true::pairBits (entry i j) []).reverse++out)

 theorem entryBody_executes (B : OracleBlock (k+7)) (entry : ℕ → ℕ → BitString)
    (n T W : ℕ) (params : Store (k+7))
    (hB : ∀ g i j out inner outer, i<n → j<n →
      ∃ c, B.Executes g (store n i j [] out inner outer params)
        (store n i j (entry i j) out inner outer params) c ∧ c≤T)
    (hW : ∀i j,i<n → j<n → (entry i j).length ≤ W)
    (g : BitString → ℕ) (i j : ℕ) (out inner outer : BitString) (hi : i<n) (hj : j<n) :
    ∃ c, (entryBody B).Executes g (store n i j [] out inner outer params)
      (store n i (j+1) [] ((true::pairBits (entry i j) []).reverse++out) inner outer params) c ∧ c≤T+6*W+12 := by
  obtain ⟨c,hc,hcb⟩ := hB g i j out inner outer hi hj
  have hp : (push (port 2) true).Executes g (store n i j [] ((true::pairBits (entry i j) []).reverse++out) inner outer params)
      (store n i (j+1) [] ((true::pairBits (entry i j) []).reverse++out) inner outer params) 1 := by
    have h := push_executes g (port 2) true (store n i j [] ((true::pairBits (entry i j) []).reverse++out) inner outer params)
    have hget : store n i j [] ((true::pairBits (entry i j) []).reverse++out) inner outer params (port 2)=List.replicate j true := by simp
    rw [hget,store_column] at h
    exact h
  exact ⟨c+(6*(entry i j).length+7+1+2)+2,seq_executes _ _ g hc
    (seq_executes _ _ g (emitWord_executes g n i j (entry i j) out inner outer params) hp),by have := hW i j hi hj;omega⟩

 theorem row_loop (B : OracleBlock (k+7)) (entry : ℕ → ℕ → BitString)
    (n T W : ℕ) (params : Store (k+7))
    (hB : ∀ g i j out inner outer, i<n → j<n →
      ∃ c, B.Executes g (store n i j [] out inner outer params)
        (store n i j (entry i j) out inner outer params) c ∧ c≤T)
    (hW : ∀i j,i<n → j<n → (entry i j).length ≤ W)
    (g : BitString → ℕ) (i j m : ℕ) (out outer : BitString) (hi : i<n) (hjm : j+m≤n) :
    ∃ c, WhileExecution (port 5) (entryBody B) (entryBody B) g
      (store n i j [] out (List.replicate m true) outer params)
      (store n i (j+m) [] (rowOutput entry i j m out) [] outer params) c ∧ c≤m*(T+6*W+14)+1 := by
  induction m generalizing j out with
  | zero =>
    refine ⟨1,?_,by simp⟩
    simpa [rowOutput] using (WhileExecution.empty (stack := port 5) (B := entryBody B) (C := entryBody B)
      (g := g) (store n i j [] out [] outer params) (by simp))
  | succ m ih =>
    obtain ⟨c,hc,hcb⟩ := entryBody_executes B entry n T W params hB hW g i j out (List.replicate m true) outer hi (by omega)
    obtain ⟨d,hd,hdb⟩ := ih (j+1) ((true::pairBits (entry i j) []).reverse++out) (by omega)
    have he : Function.update (store n i j [] out (List.replicate (m+1) true) outer params) (port 5) (List.replicate m true)=
        store n i j [] out (List.replicate m true) outer params := store_inner _ _ _ _ _ _ _ _ _
    have hh := WhileExecution.one
      (stack := port 5) (B := entryBody B) (C := entryBody B) (g := g)
      (show store n i j [] out (List.replicate (m+1) true) outer params (port 5)=true::List.replicate m true by simp [List.replicate_succ])
      (by rw [he];exact hc) hd
    refine ⟨1+c+1+d,?_,?_⟩
    · convert hh using 1 <;> simp [rowOutput,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
    · nlinarith

end HiddenCircuits.Approximation.Initialization.WordMatrixEmitter
