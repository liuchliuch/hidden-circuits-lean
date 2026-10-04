import HiddenCircuits.Complexity.GridRuntime.Outer

/-! Master-only initialization, actual grid traversal, and metadata cleanup. -/
namespace HiddenCircuits.Complexity.GridRuntime
open OracleBlock
variable {k : ℕ}

def initialStore (n m : ℕ) (d : Frame k) : Store (k+8) := fun r =>
  if r.val=0 then List.replicate n true else if r.val=1 then List.replicate m true
  else if h:9≤r.val then d ⟨r.val-9,by have := r.isLt;omega⟩ else []

noncomputable def initializeBlock : OracleBlock (k+8) :=
  seq (copyOn (port 0) (port 3) (port 8) (by simp [port]) (by simp [port]) (by simp [port]))
    (copyOn (port 1) (port 5) (port 8) (by simp [port]) (by simp [port]) (by simp [port]))
noncomputable def cleanup : OracleBlock (k+8) := seq (clear (port 2)) (clear (port 5))
noncomputable def program (B : OracleBlock (k+8)) : OracleBlock (k+8) :=
  seq initializeBlock (seq (gridBlock B) cleanup)

theorem initialize_executes (g : BitString → ℕ) (n m : ℕ) (d : Frame k) :
    initializeBlock.Executes g (initialStore n m d) (store n m 0 0 [] [] d) (5*n+5*m+6) := by
  let s₀ := initialStore n m d
  let s₁ := Function.update s₀ (port 3) (List.replicate n true)
  have h₁ : (copyOn (port (k:=k) 0) (port 3) (port 8) (by simp [port]) (by simp [port]) (by simp [port])).Executes g s₀ s₁ (5*n+2) := by
    simpa [s₀,s₁,initialStore,port] using copyOn_executes g (port (k:=k) 0) (port 3) (port 8)
      (by simp [port]) (by simp [port]) (by simp [port]) s₀ (by simp [s₀,initialStore,port])
  have h₂ : (copyOn (port (k:=k) 1) (port 5) (port 8) (by simp [port]) (by simp [port]) (by simp [port])).Executes g s₁
      (Function.update s₁ (port 5) (List.replicate m true)) (5*m+2) := by
    simpa [s₁,s₀,initialStore,port,Function.update_apply,Fin.ext_iff] using copyOn_executes g
      (port (k:=k) 1) (port 5) (port 8) (by simp [port]) (by simp [port]) (by simp [port]) s₁
      (by simp [s₁,s₀,initialStore,port,Function.update_apply,Fin.ext_iff])
  have he : Function.update s₁ (port 5) (List.replicate m true)=store n m 0 0 [] [] d := by
    funext r
    by_cases h:r.val<9
    · interval_cases hr:r.val <;> simp [s₁,s₀,initialStore,store,port,Function.update_apply,Fin.ext_iff,hr]
    · simp [s₁,s₀,initialStore,store,port,Function.update_apply,Fin.ext_iff,show r.val≠0 by omega,
        show r.val≠1 by omega,show r.val≠2 by omega,show r.val≠3 by omega,show r.val≠4 by omega,
        show r.val≠5 by omega,show r.val≠6 by omega,show r.val≠7 by omega]
  rw [he] at h₂
  convert seq_executes _ _ g h₁ h₂ using 1 <;> omega

theorem cleanup_executes (g : BitString → ℕ) (n m : ℕ) (d : Frame k) :
    cleanup.Executes g (store n m (n+1) 0 [] [] d) (initialStore n m d) (n+m+5) := by
  let s₀ := store n m (n+1) 0 [] [] d
  let s₁ := Function.update s₀ (port 2) []
  let s₂ := Function.update s₁ (port 5) []
  have h₁ : (clear (port (k:=k) 2)).Executes g s₀ s₁ (n+2) := by
    simpa [s₀,store,port] using clear_executes g (port (k:=k) 2) s₀
  have h₂ : (clear (port (k:=k) 5)).Executes g s₁ s₂ (m+1) := by
    simpa [s₁,s₀,store,port,Function.update_apply,Fin.ext_iff] using clear_executes g (port (k:=k) 5) s₁
  have he : s₂=initialStore n m d := by
    funext r
    by_cases h:r.val<9
    · interval_cases hr:r.val <;> simp [s₂,s₁,s₀,initialStore,store,port,Function.update_apply,Fin.ext_iff,hr]
    · simp [s₂,s₁,s₀,initialStore,store,port,Function.update_apply,Fin.ext_iff,show r.val≠0 by omega,
        show r.val≠1 by omega,show r.val≠2 by omega,show r.val≠3 by omega,show r.val≠4 by omega,
        show r.val≠5 by omega,show r.val≠6 by omega,show r.val≠7 by omega]
  rw [he] at h₂
  convert seq_executes _ _ g h₁ h₂ using 1 <;> omega

def programCost (n m C : ℕ) : ℕ := gridCost n m C+6*n+6*m+15

/-- Only n,m and the application frame need be supplied. Every loop index,
complement, clock and temporary is initialized by real instructions and cleared. -/
theorem program_executes (B : OracleBlock (k+8)) (g : BitString → ℕ) (n m C : ℕ)
    (states : ℕ → ℕ → Frame k) (hB : BodySpec B g n m C states)
    (hrow : ∀ i, i≤n → states i (m+1)=states (i+1) 0) :
    ∃ c, (program B).Executes g (initialStore n m (states 0 0))
      (initialStore n m (states (n+1) 0)) c ∧ c≤programCost n m C := by
  obtain ⟨c,hc,hcb⟩ := grid_executes B g n m C states hB hrow
  have hi := initialize_executes g n m (states 0 0)
  have hd := cleanup_executes g n m (states (n+1) 0)
  exact ⟨(5*n+5*m+6)+(c+(n+m+5)+2)+2,seq_executes _ _ g hi (seq_executes _ _ g hc hd),by unfold programCost;omega⟩

theorem program_queryFree (B : OracleBlock (k+8)) (hB : B.QueryFree) : (program B).QueryFree :=
  seq_queryFree _ _ (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (copyOn_queryFree _ _ _ _ _ _))
    (seq_queryFree _ _ (grid_queryFree B hB) (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _)))

theorem programCost_bound (n m C L : ℕ) (hn : n≤L) (hm : m≤L) :
    programCost n m C≤(L+1)^2*(C+40)+20*L+30 := by
  unfold programCost gridCost
  have h₁ : (n+1)*(m+1)≤(L+1)^2 := by simpa [pow_two] using Nat.mul_le_mul (by omega : n+1≤L+1) (by omega : m+1≤L+1)
  have h₂ := Nat.mul_le_mul_right (C+6) h₁
  have h₃ : (n+1)*(11*m+22)≤22*(L+1)^2 := by
    have := Nat.mul_le_mul (by omega : n+1≤L+1) (by omega : 11*m+22≤22*(L+1))
    nlinarith
  nlinarith
end HiddenCircuits.Complexity.GridRuntime
