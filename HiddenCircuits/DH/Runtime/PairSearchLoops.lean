import HiddenCircuits.DH.Runtime.PairSearchCell

/-! Actual nested unary loops for row-major first-success search. -/
namespace HiddenCircuits.DH.Runtime.PairSearch
open Complexity Complexity.OracleBlock PairCheck

noncomputable def rowLoop : OracleBlock 30 := whilePop 29 body body
noncomputable def rowBody : OracleBlock 30 := seq (copyOn 0 29 30 (by decide) (by decide) (by decide))
  (seq rowLoop (seq (clear 7) (push 6 true)))
noncomputable def rowsLoop : OracleBlock 30 := whilePop 28 rowBody rowBody

def rowBudget (n : ℕ) : ℕ := n*(bodyBudget n+2)+6*n+11

lemma pop_inner {n : ℕ} (payload marks : BitString) (found : Option (PruningModel.Action n))
    (u v : ℕ) (outerClock innerClock : BitString) (b : Bool) :
    Function.update (state (n:=n) payload marks found u v outerClock (b::innerClock)) 29 innerClock=
      state (n:=n) payload marks found u v outerClock innerClock := by
  funext i;fin_cases i <;> rfl

lemma pop_outer {n : ℕ} (payload marks : BitString) (found : Option (PruningModel.Action n))
    (u v : ℕ) (outerClock innerClock : BitString) (b : Bool) :
    Function.update (state (n:=n) payload marks found u v (b::outerClock) innerClock) 28 outerClock=
      state (n:=n) payload marks found u v outerClock innerClock := by
  funext i;fin_cases i <;> rfl

lemma rowLoop_execution (g : BitString → ℕ) {n : ℕ} (G : MatrixData n) (alive : Vector Bool n)
    (u : Fin n) (j m : ℕ) (hjm : j+m≤n) (found : Option (PruningModel.Action n)) (outerClock : BitString) :
    ∃t, WhileExecution (29 : Fin 31) body body g
      (state (n:=n) G.bits (liveBits alive) found u.val j outerClock (List.replicate m true))
      (state (n:=n) G.bits (liveBits alive) (rowFrom G alive u j m found) u.val (j+m) outerClock []) t ∧
      t≤m*(bodyBudget n+2)+1 := by
  induction m generalizing j found with
  | zero => exact ⟨1,by simpa [rowFrom] using (WhileExecution.empty
      (state (n:=n) G.bits (liveBits alive) found u.val j outerClock []) rfl),by simp⟩
  | succ m ih =>
    have hj : j<n := by omega
    let v : Fin n := ⟨j,hj⟩
    obtain ⟨c,hc,hbc⟩ := body_executes g G alive u v found outerClock (List.replicate m true)
    obtain ⟨t,ht,hbt⟩ := ih (j+1) (by omega) (step G alive u v found)
    have hh := WhileExecution.one
      (show state (n:=n) G.bits (liveBits alive) found u.val j outerClock (List.replicate (m+1) true) 29=
        true::List.replicate m true from rfl)
      (by simpa only [List.replicate_succ,pop_inner] using hc) ht
    refine ⟨1+c+1+t,?_,?_⟩
    · have he : j+1+m=j+(m+1) := by omega
      simpa only [rowFrom,dif_pos hj,he] using hh
    · simp only [Nat.add_mul,Nat.one_mul];omega

lemma rowBody_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n) (alive : Vector Bool n)
    (u : Fin n) (found : Option (PruningModel.Action n)) (outerClock : BitString) :
    ∃t, rowBody.Executes g (state (n:=n) G.bits (liveBits alive) found u.val 0 outerClock [])
      (state (n:=n) G.bits (liveBits alive) (rowFrom G alive u 0 n found) (u.val+1) 0 outerClock []) t ∧
      t≤rowBudget n := by
  have h1 : (copyOn (0 : Fin 31) 29 30 (by decide) (by decide) (by decide)).Executes g
      (state (n:=n) G.bits (liveBits alive) found u.val 0 outerClock [])
      (state (n:=n) G.bits (liveBits alive) found u.val 0 outerClock (List.replicate n true)) (5*n+2) := by
    convert copyOn_executes g (0 : Fin 31) 29 30 (by decide) (by decide) (by decide)
      (state (n:=n) G.bits (liveBits alive) found u.val 0 outerClock []) rfl using 1
    · funext i;fin_cases i <;> simp [state,rawState]
    · simp [state,rawState]
  obtain ⟨c,hc,hbc⟩ := rowLoop_execution g G alive u 0 n (by omega) found outerClock
  have h2 : rowLoop.Executes g (state (n:=n) G.bits (liveBits alive) found u.val 0 outerClock (List.replicate n true))
      (state (n:=n) G.bits (liveBits alive) (rowFrom G alive u 0 n found) u.val n outerClock []) c := by
    simpa only [Nat.zero_add] using whilePop_executes _ _ _ g hc
  have h3 : (clear (7 : Fin 31)).Executes g
      (state (n:=n) G.bits (liveBits alive) (rowFrom G alive u 0 n found) u.val n outerClock [])
      (state (n:=n) G.bits (liveBits alive) (rowFrom G alive u 0 n found) u.val 0 outerClock []) (n+1) := by
    convert clear_executes g (7 : Fin 31)
      (state (n:=n) G.bits (liveBits alive) (rowFrom G alive u 0 n found) u.val n outerClock []) using 1
    · funext i;fin_cases i <;> simp [state,rawState]
    · simp [state,rawState]
  have h4 : (push (6 : Fin 31) true).Executes g
      (state (n:=n) G.bits (liveBits alive) (rowFrom G alive u 0 n found) u.val 0 outerClock [])
      (state (n:=n) G.bits (liveBits alive) (rowFrom G alive u 0 n found) (u.val+1) 0 outerClock []) 1 := by
    convert push_executes g (6 : Fin 31) true
      (state (n:=n) G.bits (liveBits alive) (rowFrom G alive u 0 n found) u.val 0 outerClock []) using 1
    funext i;fin_cases i <;> simp [state,rawState,List.replicate_succ]
  exact ⟨(5*n+2)+(c+((n+1)+1+2)+2)+2,
    seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)),by unfold rowBudget;omega⟩

lemma rowsLoop_execution (g : BitString → ℕ) {n : ℕ} (G : MatrixData n) (alive : Vector Bool n)
    (i m : ℕ) (him : i+m≤n) (found : Option (PruningModel.Action n)) :
    ∃t, WhileExecution (28 : Fin 31) rowBody rowBody g
      (state (n:=n) G.bits (liveBits alive) found i 0 (List.replicate m true) [])
      (state (n:=n) G.bits (liveBits alive) (rowsFrom G alive i m found) (i+m) 0 [] []) t ∧
      t≤m*(rowBudget n+2)+1 := by
  induction m generalizing i found with
  | zero => exact ⟨1,by simpa [rowsFrom] using (WhileExecution.empty
      (state (n:=n) G.bits (liveBits alive) found i 0 [] []) rfl),by simp⟩
  | succ m ih =>
    have hi : i<n := by omega
    let u : Fin n := ⟨i,hi⟩
    obtain ⟨c,hc,hbc⟩ := rowBody_executes g G alive u found (List.replicate m true)
    obtain ⟨t,ht,hbt⟩ := ih (i+1) (by omega) (rowFrom G alive u 0 n found)
    have hh := WhileExecution.one
      (show state (n:=n) G.bits (liveBits alive) found i 0 (List.replicate (m+1) true) [] 28=
        true::List.replicate m true from rfl)
      (by simpa only [List.replicate_succ,pop_outer] using hc) ht
    refine ⟨1+c+1+t,?_,?_⟩
    · have he : i+1+m=i+(m+1) := by omega
      simpa only [rowsFrom,dif_pos hi,he] using hh
    · simp only [Nat.add_mul,Nat.one_mul];omega

lemma rowLoop_queryFree : rowLoop.QueryFree := whilePop_queryFree _ _ _ body_queryFree body_queryFree
lemma rowBody_queryFree : rowBody.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ rowLoop_queryFree (seq_queryFree _ _ (clear_queryFree _) (push_queryFree _ _)))
lemma rowsLoop_queryFree : rowsLoop.QueryFree := whilePop_queryFree _ _ _ rowBody_queryFree rowBody_queryFree

end HiddenCircuits.DH.Runtime.PairSearch
