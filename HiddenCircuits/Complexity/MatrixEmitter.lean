import HiddenCircuits.Complexity.OracleLibrary
import HiddenCircuits.Complexity.OracleBlockNoQuery

/-! A finite framed row-major matrix emitter; callbacks are genuine verified bit programs. -/
namespace HiddenCircuits.Complexity.MatrixEmitter
open OracleBlock
variable {k : ℕ}

def port (i : Fin 8) : Fin (k+8) := ⟨i.val,by omega⟩

/-- Eight reserved registers followed by arbitrary framed callback parameters. -/
def store (n i j : ℕ) (bit out inner outer : BitString) (params : Store (k+7)) : Store (k+7) :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update params
      (port 0) (List.replicate n true)) (port 1) (List.replicate i true))
      (port 2) (List.replicate j true)) (port 3) bit) (port 4) out)
      (port 5) inner) (port 6) outer) (port 7) []

@[simp] theorem store_core (n i j : ℕ) (bit out inner outer : BitString) (params : Store (k+7)) (r : Fin 8) :
    store n i j bit out inner outer params (port r)=
      (![List.replicate n true,List.replicate i true,List.replicate j true,bit,out,inner,outer,[]] : Fin 8 → BitString) r := by
  fin_cases r <;> simp [store,port]

 theorem store_column (n i j : ℕ) (bit out inner outer : BitString) (params : Store (k+7)) :
    Function.update (store n i j bit out inner outer params) (port 2) (true::List.replicate j true)=
      store n i (j+1) bit out inner outer params := by
  funext r
  simp [store,Function.update_apply,List.replicate_succ]
  split_ifs <;> simp_all [port]

 theorem store_inner (n i j : ℕ) (bit out inner outer next : BitString) (params : Store (k+7)) :
    Function.update (store n i j bit out inner outer params) (port 5) next=store n i j bit out next outer params := by
  funext r
  simp [store,Function.update_apply]
  split_ifs <;> simp_all [port]

noncomputable def emitBit : OracleBlock (k+7) :=
  branchPop (port 3) skip (push (port 4) false) (push (port 4) true)

 theorem emitBit_executes (g : BitString → ℕ) (n i j : ℕ) (b : Bool)
    (out inner outer : BitString) (params : Store (k+7)) :
    emitBit.Executes g (store n i j [b] out inner outer params)
      (store n i j [] (b::out) inner outer params) 3 := by
  let s := store n i j [b] out inner outer params
  have hs : s (port 3)=b::[] := by simp [s]
  have he : Function.update s (port 3) []=store n i j [] out inner outer params := by
    funext r
    simp [s,store,Function.update_apply]
    split_ifs <;> simp_all [port]
  have hp : (push (port 4) b).Executes g (Function.update s (port 3) [])
      (store n i j [] (b::out) inner outer params) 1 := by
    rw [he]
    convert push_executes g (port 4) b (store n i j [] out inner outer params) using 1
    funext r
    simp [store,Function.update_apply]
    split_ifs <;> simp_all [port]
  cases b
  · exact branchPop_false _ _ _ _ g hs hp
  · exact branchPop_true _ _ _ _ g hs hp

noncomputable def entryBody (B : OracleBlock (k+7)) : OracleBlock (k+7) :=
  seq B (seq emitBit (push (port 2) true))
noncomputable def rowLoop (B : OracleBlock (k+7)) : OracleBlock (k+7) :=
  whilePop (port 5) (entryBody B) (entryBody B)

def rowOutput (edge : ℕ → ℕ → Bool) (i : ℕ) : ℕ → ℕ → BitString → BitString
  | _,0,out => out
  | j,m+1,out => rowOutput edge i (j+1) m (edge i j::out)

 theorem entryBody_executes (B : OracleBlock (k+7)) (edge : ℕ → ℕ → Bool)
    (n T : ℕ) (params : Store (k+7))
    (hB : ∀ g i j out inner outer, i<n → j<n →
      ∃ c, B.Executes g (store n i j [] out inner outer params)
        (store n i j [edge i j] out inner outer params) c ∧ c≤T)
    (g : BitString → ℕ) (i j : ℕ) (out inner outer : BitString) (hi : i<n) (hj : j<n) :
    ∃ c, (entryBody B).Executes g (store n i j [] out inner outer params)
      (store n i (j+1) [] (edge i j::out) inner outer params) c ∧ c≤T+8 := by
  obtain ⟨c,hc,hcb⟩ := hB g i j out inner outer hi hj
  have hp : (push (port 2) true).Executes g (store n i j [] (edge i j::out) inner outer params)
      (store n i (j+1) [] (edge i j::out) inner outer params) 1 := by
    have h := push_executes g (port 2) true (store n i j [] (edge i j::out) inner outer params)
    have hget : store n i j [] (edge i j::out) inner outer params (port 2)=List.replicate j true := by simp
    rw [hget,store_column] at h
    exact h
  exact ⟨c+(3+1+2)+2,seq_executes _ _ g hc
    (seq_executes _ _ g (emitBit_executes g n i j (edge i j) out inner outer params) hp),by omega⟩

 theorem row_loop (B : OracleBlock (k+7)) (edge : ℕ → ℕ → Bool)
    (n T : ℕ) (params : Store (k+7))
    (hB : ∀ g i j out inner outer, i<n → j<n →
      ∃ c, B.Executes g (store n i j [] out inner outer params)
        (store n i j [edge i j] out inner outer params) c ∧ c≤T)
    (g : BitString → ℕ) (i j m : ℕ) (out outer : BitString) (hi : i<n) (hjm : j+m≤n) :
    ∃ c, WhileExecution (port 5) (entryBody B) (entryBody B) g
      (store n i j [] out (List.replicate m true) outer params)
      (store n i (j+m) [] (rowOutput edge i j m out) [] outer params) c ∧ c≤m*(T+10)+1 := by
  induction m generalizing j out with
  | zero =>
    refine ⟨1,?_,by simp⟩
    simpa [rowOutput] using (WhileExecution.empty (stack := port 5) (B := entryBody B) (C := entryBody B)
      (g := g) (store n i j [] out [] outer params) (by simp))
  | succ m ih =>
    obtain ⟨c,hc,hcb⟩ := entryBody_executes B edge n T params hB g i j out (List.replicate m true) outer hi (by omega)
    obtain ⟨d,hd,hdb⟩ := ih (j+1) (edge i j::out) (by omega)
    have he : Function.update (store n i j [] out (List.replicate (m+1) true) outer params) (port 5) (List.replicate m true)=
        store n i j [] out (List.replicate m true) outer params := store_inner _ _ _ _ _ _ _ _ _
    have hh := WhileExecution.one
      (stack := port 5) (B := entryBody B) (C := entryBody B) (g := g)
      (show store n i j [] out (List.replicate (m+1) true) outer params (port 5)=true::List.replicate m true by simp [List.replicate_succ])
      (by rw [he];exact hc) hd
    refine ⟨1+c+1+d,?_,?_⟩
    · convert hh using 1 <;> simp [rowOutput,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
    · nlinarith

end HiddenCircuits.Complexity.MatrixEmitter
