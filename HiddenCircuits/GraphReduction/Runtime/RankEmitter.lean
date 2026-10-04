import HiddenCircuits.Complexity.MatrixEmitterSerialization
import HiddenCircuits.Complexity.BinaryArithmetic.WeightStreamsEmit

/-! Actual comparison scans emitting two unary payload bits per true result. -/
namespace HiddenCircuits.GraphReduction.Runtime.RankEmitter
open Complexity OracleBlock MatrixEmitter BinaryArithmetic
variable {k : ℕ}
set_option maxHeartbeats 700000

noncomputable def emitCount : OracleBlock (k+7) := branchPop (port 3) skip skip (seq (push (port 4) true) (push (port 4) true))
def increment (b : Bool) (out : BitString) : BitString := if b then true::true::out else out

lemma emitCount_executes (g : BitString → ℕ) (n i j : ℕ) (b : Bool) (out inner outer : BitString) (params : Store (k+7)) :
    ∃c,emitCount.Executes g (store n i j [b] out inner outer params)
      (store n i j [] (increment b out) inner outer params) c ∧ c≤6 := by
  have hs : store n i j [b] out inner outer params (port 3)=b::[] := by simp
  have he : Function.update (store n i j [b] out inner outer params) (port 3) []=store n i j [] out inner outer params := by
    funext r;simp [store,Function.update_apply];split_ifs <;> simp_all [port]
  cases b
  · refine ⟨3,?_,by omega⟩
    apply branchPop_false _ skip skip _ g hs
    rw [he]
    exact skip_executes _ _
  · have h₁ : (push (port 4) true).Executes g (store n i j [] out inner outer params) (store n i j [] (true::out) inner outer params) 1 := by
      simpa only [store_core,Matrix.cons_val_zero,Matrix.cons_val_succ,store_output] using push_executes g (port 4) true (store n i j [] out inner outer params)
    have h₂ : (push (port 4) true).Executes g (store n i j [] (true::out) inner outer params) (store n i j [] (true::true::out) inner outer params) 1 := by
      simpa only [store_core,Matrix.cons_val_zero,Matrix.cons_val_succ,store_output] using push_executes g (port 4) true (store n i j [] (true::out) inner outer params)
    refine ⟨6,?_,by omega⟩
    apply branchPop_true _ skip skip _ g hs
    rw [he]
    exact seq_executes _ _ g h₁ h₂

noncomputable def entry (B : OracleBlock (k+7)) : OracleBlock (k+7) := seq B (seq emitCount (push (port 2) true))
noncomputable def rowLoop (B : OracleBlock (k+7)) : OracleBlock (k+7) := whilePop (port 5) (entry B) (entry B)
def rowOutput (edge : ℕ→ℕ→Bool) (i : ℕ) : ℕ→ℕ→BitString→BitString
  | _,0,out => out
  | j,m+1,out => rowOutput edge i (j+1) m (increment (edge i j) out)
def rowCount (edge : ℕ→ℕ→Bool) (i : ℕ) : ℕ→ℕ→ℕ
  | _,0 => 0
  | j,m+1 => (if edge i j then 1 else 0)+rowCount edge i (j+1) m

lemma entry_executes (B : OracleBlock (k+7)) (edge : ℕ→ℕ→Bool) (n T : ℕ) (params : Store (k+7))
    (hB : ∀g i j out inner outer,i<n→j<n→∃c,B.Executes g (store n i j [] out inner outer params)
      (store n i j [edge i j] out inner outer params) c ∧ c≤T)
    (g : BitString→ℕ) (i j : ℕ) (out inner outer : BitString) (hi:i<n) (hj:j<n) :
    ∃c,(entry B).Executes g (store n i j [] out inner outer params)
      (store n i (j+1) [] (increment (edge i j) out) inner outer params) c ∧ c≤T+11 := by
  obtain ⟨a,ha,hab⟩ := hB g i j out inner outer hi hj
  obtain ⟨b,hb,hbb⟩ := emitCount_executes g n i j (edge i j) out inner outer params
  have hc : (push (port 2) true).Executes g (store n i j [] (increment (edge i j) out) inner outer params)
      (store n i (j+1) [] (increment (edge i j) out) inner outer params) 1 := by
    have h := push_executes g (port 2) true (store n i j [] (increment (edge i j) out) inner outer params)
    have hv : store n i j [] (increment (edge i j) out) inner outer params (port 2)=List.replicate j true := by simp
    rw [hv,store_column] at h
    exact h
  exact ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb hc),by omega⟩

lemma row_loop (B : OracleBlock (k+7)) (edge : ℕ→ℕ→Bool) (n T : ℕ) (params : Store (k+7))
    (hB : ∀g i j out inner outer,i<n→j<n→∃c,B.Executes g (store n i j [] out inner outer params)
      (store n i j [edge i j] out inner outer params) c ∧ c≤T)
    (g : BitString→ℕ) (i j m : ℕ) (out outer : BitString) (hi:i<n) (hjm:j+m≤n) :
    ∃c,WhileExecution (port 5) (entry B) (entry B) g (store n i j [] out (List.replicate m true) outer params)
      (store n i (j+m) [] (rowOutput edge i j m out) [] outer params) c ∧ c≤m*(T+13)+1 := by
  induction m generalizing j out with
  | zero => exact ⟨1,by simpa [rowOutput] using WhileExecution.empty (stack:=port 5) (B:=entry B) (C:=entry B) (g:=g) (store n i j [] out [] outer params) (by simp),by simp⟩
  | succ m ih =>
    obtain ⟨a,ha,hab⟩ := entry_executes B edge n T params hB g i j out (List.replicate m true) outer hi (by omega)
    obtain ⟨b,hb,hbb⟩ := ih (j+1) (increment (edge i j) out) (by omega)
    have he : Function.update (store n i j [] out (List.replicate (m+1) true) outer params) (port 5) (List.replicate m true)=store n i j [] out (List.replicate m true) outer params := store_inner _ _ _ _ _ _ _ _ _
    have hs := WhileExecution.one (stack:=port 5) (B:=entry B) (C:=entry B) (g:=g)
      (show store n i j [] out (List.replicate (m+1) true) outer params (port 5)=true::List.replicate m true by simp [List.replicate_succ])
      (by rw [he];exact ha) hb
    refine ⟨1+a+1+b,?_,by nlinarith⟩
    convert hs using 1 <;> simp [rowOutput,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

lemma rowCount_le (edge : ℕ→ℕ→Bool) (i j m : ℕ) : rowCount edge i j m≤m := by
  induction m generalizing j with
  | zero => rfl
  | succ m ih =>
    rw [rowCount]
    have hh:=ih (j+1)
    split_ifs <;> omega
lemma rowCount_eq (edge : ℕ→ℕ→Bool) (i j m : ℕ) : rowCount edge i j m=((List.range' j m).filter (edge i)).length := by
  induction m generalizing j with
  | zero => rfl
  | succ m ih => simp only [rowCount,List.range'_succ,List.filter_cons];split_ifs <;> simp [ih] <;> omega
lemma replicate_two_comm (n : ℕ) (out : BitString) :
    List.replicate n true++true::true::out=true::true::(List.replicate n true++out) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ,List.cons_append] using congrArg (List.cons true) ih

lemma rowOutput_eq (edge : ℕ→ℕ→Bool) (i j m : ℕ) (out : BitString) :
    rowOutput edge i j m out=List.replicate (2*rowCount edge i j m) true++out := by
  induction m generalizing j out with
  | zero => rfl
  | succ m ih =>
    rw [rowOutput,ih,rowCount]
    cases he:edge i j <;> simp [increment,he,Nat.mul_add,List.replicate_add,List.append_assoc,Nat.add_comm]
    exact replicate_two_comm _ _
end HiddenCircuits.GraphReduction.Runtime.RankEmitter
