import HiddenCircuits.Complexity.GridRuntime.Inner

/-! Literal outer loop and composed cost for the full inclusive rectangular grid. -/
namespace HiddenCircuits.Complexity.GridRuntime
open OracleBlock
variable {k : ℕ}

noncomputable def resetColumn : OracleBlock (k+8) :=
  seq (clear (port 4)) (copyOn (port 1) (port 5) (port 8) (by simp [port]) (by simp [port]) (by simp [port]))
noncomputable def rowBlock (B : OracleBlock (k+8)) : OracleBlock (k+8) :=
  seq (innerBlock B) (seq resetColumn (advance (port 2) (port 3)))
noncomputable def outerLoop (B : OracleBlock (k+8)) : OracleBlock (k+8) :=
  whilePop (port 7) (rowBlock B) (rowBlock B)
noncomputable def gridBlock (B : OracleBlock (k+8)) : OracleBlock (k+8) :=
  seq (copyOn (port 0) (port 7) (port 8) (by simp [port]) (by simp [port]) (by simp [port]))
    (seq (push (port 7) true) (outerLoop B))

theorem resetColumn_executes (g : BitString → ℕ) (n m i : ℕ) (outer : BitString) (d : Frame k) :
    resetColumn.Executes g (store n m i (m+1) [] outer d) (store n m i 0 [] outer d) (6*m+6) := by
  let s₀ := store n m i (m+1) [] outer d
  let s₁ := Function.update s₀ (port 4) []
  have h₁ : (clear (port (k:=k) 4)).Executes g s₀ s₁ (m+2) := by
    simpa [s₀,store,port] using clear_executes g (port (k:=k) 4) s₀
  have hh := copyOn_executes g (port (k:=k) 1) (port 5) (port 8) (by simp [port]) (by simp [port]) (by simp [port]) s₁
    (by simp [s₁,s₀,store,port,Function.update_apply,Fin.ext_iff])
  have he : Function.update s₁ (port 5) (List.replicate m true)=store n m i 0 [] outer d := by
    funext r
    by_cases h:r.val<9
    · interval_cases hr:r.val <;> simp [s₁,s₀,store,port,Function.update_apply,Fin.ext_iff,hr]
    · simp [s₁,s₀,store,port,Function.update_apply,Fin.ext_iff,show r.val≠0 by omega,show r.val≠1 by omega,
        show r.val≠2 by omega,show r.val≠3 by omega,show r.val≠4 by omega,show r.val≠5 by omega,
        show r.val≠6 by omega,show r.val≠7 by omega]
  have h₂ : (copyOn (port (k:=k) 1) (port 5) (port 8) (by simp [port]) (by simp [port]) (by simp [port])).Executes g s₁
      (store n m i 0 [] outer d) (5*m+2) := by
    have hh' : (copyOn (port (k:=k) 1) (port 5) (port 8) (by simp [port]) (by simp [port]) (by simp [port])).Executes g s₁
        (Function.update s₁ (port 5) (List.replicate m true)) (5*m+2) := by
      simpa [s₁,s₀,store,port,Function.update_apply,Fin.ext_iff] using hh
    rwa [he] at hh'
  convert seq_executes _ _ g h₁ h₂ using 1 <;> omega

def rowCost (m C : ℕ) : ℕ := (m+1)*(C+6)+11*m+20

theorem row_executes (B : OracleBlock (k+8)) (g : BitString → ℕ) (n m C : ℕ)
    (states : ℕ → ℕ → Frame k) (hB : BodySpec B g n m C states)
    (hrow : ∀ i, i≤n → states i (m+1)=states (i+1) 0)
    (i : ℕ) (hi : i≤n) (outer : BitString) :
    ∃ c, (rowBlock B).Executes g (store n m i 0 [] outer (states i 0))
      (store n m (i+1) 0 [] outer (states (i+1) 0)) c ∧ c≤rowCost m C := by
  obtain ⟨c,hc,hcb⟩ := inner_executes B g n m C states hB i hi outer
  have hr := resetColumn_executes g n m i outer (states i (m+1))
  have ha := advance_executes g (port (k:=k) 2) (port 3) (by simp [port])
    (store n m i 0 [] outer (states i (m+1)))
  rw [store_advance_row] at ha
  have hh := seq_executes _ _ g hc (seq_executes _ _ g hr ha)
  rw [hrow i hi] at hh
  exact ⟨c+((6*m+6)+2+2)+2,hh,by unfold rowCost;omega⟩

theorem outer_loop (B : OracleBlock (k+8)) (g : BitString → ℕ) (n m C : ℕ)
    (states : ℕ → ℕ → Frame k) (hB : BodySpec B g n m C states)
    (hrow : ∀ i, i≤n → states i (m+1)=states (i+1) 0)
    (i r : ℕ) (hir : i+r≤n+1) :
    ∃ c, WhileExecution (port 7) (rowBlock B) (rowBlock B) g
      (store n m i 0 [] (List.replicate r true) (states i 0))
      (store n m (i+r) 0 [] [] (states (i+r) 0)) c ∧ c≤r*(rowCost m C+2)+1 := by
  induction r generalizing i with
  | zero =>
    refine ⟨1,?_,by simp⟩
    simpa using (WhileExecution.empty (stack:=port (k:=k) 7) (B:=rowBlock B) (C:=rowBlock B)
      (g:=g) (store n m i 0 [] [] (states i 0)) (by simp [store,port]))
  | succ r ih =>
    obtain ⟨c,hc,hcb⟩ := row_executes B g n m C states hB hrow i (by omega) (List.replicate r true)
    obtain ⟨t,ht,htb⟩ := ih (i+1) (by omega)
    have hc' : (rowBlock B).Executes g
        (Function.update (store n m i 0 [] (List.replicate (r+1) true) (states i 0)) (port 7) (List.replicate r true))
        (store n m (i+1) 0 [] (List.replicate r true) (states (i+1) 0)) c := by
      rw [store_update_outer];exact hc
    have hh := WhileExecution.one
      (show store n m i 0 [] (List.replicate (r+1) true) (states i 0) (port 7)=true::List.replicate r true by simp [store,port,List.replicate_succ])
      hc' ht
    refine ⟨1+c+1+t,?_,by nlinarith⟩
    simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hh

def gridCost (n m C : ℕ) : ℕ := (n+1)*((m+1)*(C+6)+11*m+22)+5*n+8

/-- Exactly all inclusive pairs (0,0),...,(n,m) are visited by one fixed finite program. -/
theorem grid_executes (B : OracleBlock (k+8)) (g : BitString → ℕ) (n m C : ℕ)
    (states : ℕ → ℕ → Frame k) (hB : BodySpec B g n m C states)
    (hrow : ∀ i, i≤n → states i (m+1)=states (i+1) 0) :
    ∃ c, (gridBlock B).Executes g (store n m 0 0 [] [] (states 0 0))
      (store n m (n+1) 0 [] [] (states (n+1) 0)) c ∧ c≤gridCost n m C := by
  let d := states 0 0
  let s₀ := store n m 0 0 [] [] d
  let s₁ := store n m 0 0 [] (List.replicate n true) d
  let s₂ := store n m 0 0 [] (List.replicate (n+1) true) d
  have hh := copyOn_executes g (port (k:=k) 0) (port 7) (port 8) (by simp [port]) (by simp [port]) (by simp [port]) s₀
    (by simp [s₀,store,port])
  have h₁ : (copyOn (port (k:=k) 0) (port 7) (port 8) (by simp [port]) (by simp [port]) (by simp [port])).Executes g s₀ s₁ (5*n+2) := by
    have he : Function.update s₀ (port 7) (List.replicate n true)=s₁ := store_update_outer n m 0 0 [] [] _ d
    have hh' : (copyOn (port (k:=k) 0) (port 7) (port 8) (by simp [port]) (by simp [port]) (by simp [port])).Executes g s₀
        (Function.update s₀ (port 7) (List.replicate n true)) (5*n+2) := by simpa [s₀,store,port] using hh
    rwa [he] at hh'
  have h₂ : (push (port (k:=k) 7) true).Executes g s₁ s₂ 1 := by
    have hh := push_executes g (port (k:=k) 7) true s₁
    have he : Function.update s₁ (port 7) (true::s₁ (port 7))=s₂ := by
      change Function.update (store n m 0 0 [] (List.replicate n true) d) (port 7) _=_
      rw [store_update_outer]
      simp [s₁,s₂,store,port,List.replicate_succ]
    rwa [he] at hh
  obtain ⟨c,hc,hcb⟩ := outer_loop B g n m C states hB hrow 0 (n+1) (by omega)
  have h₃ := whilePop_executes _ _ _ g hc
  refine ⟨(5*n+2)+(1+c+2)+2,?_,by unfold gridCost rowCost at *;nlinarith⟩
  simpa only [Nat.zero_add] using seq_executes _ _ g h₁ (seq_executes _ _ g h₂ h₃)

theorem grid_queryFree (B : OracleBlock (k+8)) (hB : B.QueryFree) : (gridBlock B).QueryFree := by
  have hr : (rowBlock B).QueryFree := seq_queryFree _ _ (inner_queryFree B hB)
    (seq_queryFree _ _ (seq_queryFree _ _ (clear_queryFree _) (copyOn_queryFree _ _ _ _ _ _)) (advance_queryFree _ _))
  exact seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (push_queryFree _ _) (whilePop_queryFree _ _ _ hr hr))
end HiddenCircuits.Complexity.GridRuntime
