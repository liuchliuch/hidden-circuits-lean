import HiddenCircuits.Complexity.GridRuntime.Basic

/-! A real inner grid loop with increasing index and decreasing unary complement. -/
namespace HiddenCircuits.Complexity.GridRuntime
open OracleBlock
variable {k : ℕ}

noncomputable def cellBlock (B : OracleBlock (k+8)) : OracleBlock (k+8) :=
  seq B (advance (port 4) (port 5))
noncomputable def innerLoop (B : OracleBlock (k+8)) : OracleBlock (k+8) :=
  whilePop (port 6) (cellBlock B) (cellBlock B)
noncomputable def innerBlock (B : OracleBlock (k+8)) : OracleBlock (k+8) :=
  seq (copyOn (port 1) (port 6) (port 8) (by simp [port]) (by simp [port]) (by simp [port]))
    (seq (push (port 6) true) (innerLoop B))

def foldRow (f : ℕ → ℕ → Frame k → Frame k) (i : ℕ) : ℕ → ℕ → Frame k → Frame k
  | _,0,d => d
  | j,r+1,d => foldRow f i (j+1) r (f i j d)

/-- The real body is checked at each semantic prefix state. Prefix states may
contain arbitrarily large data, but their established invariant supplies C. -/
def BodySpec (B : OracleBlock (k+8)) (g : BitString → ℕ) (n m C : ℕ)
    (states : ℕ → ℕ → Frame k) : Prop :=
  ∀ i j, i≤n → j≤m → ∀ inner outer, ∃ c,
    B.Executes g (store n m i j inner outer (states i j))
      (store n m i j inner outer (states i (j+1))) c ∧ c≤C

theorem cell_executes (B : OracleBlock (k+8)) (g : BitString → ℕ) (n m C : ℕ)
    (states : ℕ → ℕ → Frame k) (hB : BodySpec B g n m C states)
    (i j : ℕ) (hi : i≤n) (hj : j≤m) (inner outer : BitString) :
    ∃ c, (cellBlock B).Executes g (store n m i j inner outer (states i j))
      (store n m i (j+1) inner outer (states i (j+1))) c ∧ c≤C+4 := by
  obtain ⟨c,hc,hcb⟩ := hB i j hi hj inner outer
  have ha := advance_executes g (port (k:=k) 4) (port 5) (by simp [port])
    (store n m i j inner outer (states i (j+1)))
  rw [store_advance_column] at ha
  exact ⟨c+2+2,seq_executes _ _ g hc ha,by omega⟩

theorem inner_loop (B : OracleBlock (k+8)) (g : BitString → ℕ) (n m C : ℕ)
    (states : ℕ → ℕ → Frame k) (hB : BodySpec B g n m C states)
    (i j r : ℕ) (hi : i≤n) (hjr : j+r≤m+1) (outer : BitString) :
    ∃ c, WhileExecution (port 6) (cellBlock B) (cellBlock B) g
      (store n m i j (List.replicate r true) outer (states i j))
      (store n m i (j+r) [] outer (states i (j+r))) c ∧ c≤r*(C+6)+1 := by
  induction r generalizing j with
  | zero =>
    refine ⟨1,?_,by simp⟩
    simpa using (WhileExecution.empty (stack:=port (k:=k) 6) (B:=cellBlock B) (C:=cellBlock B)
      (g:=g) (store n m i j [] outer (states i j)) (by simp [store,port]))
  | succ r ih =>
    obtain ⟨c,hc,hcb⟩ := cell_executes B g n m C states hB i j hi (by omega) (List.replicate r true) outer
    obtain ⟨t,ht,htb⟩ := ih (j+1) (by omega)
    have hc' : (cellBlock B).Executes g
        (Function.update (store n m i j (List.replicate (r+1) true) outer (states i j)) (port 6) (List.replicate r true))
        (store n m i (j+1) (List.replicate r true) outer (states i (j+1))) c := by
      rw [store_update_inner];exact hc
    have hh := WhileExecution.one
      (show store n m i j (List.replicate (r+1) true) outer (states i j) (port 6)=true::List.replicate r true by simp [store,port,List.replicate_succ])
      hc' ht
    refine ⟨1+c+1+t,?_,by nlinarith⟩
    simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hh

theorem inner_executes (B : OracleBlock (k+8)) (g : BitString → ℕ) (n m C : ℕ)
    (states : ℕ → ℕ → Frame k) (hB : BodySpec B g n m C states)
    (i : ℕ) (hi : i≤n) (outer : BitString) :
    ∃ c, (innerBlock B).Executes g (store n m i 0 [] outer (states i 0))
      (store n m i (m+1) [] outer (states i (m+1))) c ∧ c≤(m+1)*(C+6)+5*m+8 := by
  let d := states i 0
  let s₀ := store n m i 0 [] outer d
  let s₁ := store n m i 0 (List.replicate m true) outer d
  let s₂ := store n m i 0 (List.replicate (m+1) true) outer d
  have h₁ : (copyOn (port (k:=k) 1) (port 6) (port 8) (by simp [port]) (by simp [port]) (by simp [port])).Executes g s₀ s₁ (5*m+2) := by
    have hh := copyOn_executes g (port (k:=k) 1) (port 6) (port 8) (by simp [port]) (by simp [port]) (by simp [port]) s₀ (by simp [s₀,store,port])
    have he : Function.update s₀ (port 6) (List.replicate m true)=s₁ := store_update_inner n m i 0 [] outer _ d
    have hh' : (copyOn (port (k:=k) 1) (port 6) (port 8) (by simp [port]) (by simp [port]) (by simp [port])).Executes g s₀
        (Function.update s₀ (port 6) (List.replicate m true)) (5*m+2) := by
      simpa [s₀,store,port] using hh
    rwa [he] at hh'
  have h₂ : (push (port (k:=k) 6) true).Executes g s₁ s₂ 1 := by
    have hh := push_executes g (port (k:=k) 6) true s₁
    have he : Function.update s₁ (port 6) (true::s₁ (port 6))=s₂ := by
      change Function.update (store n m i 0 (List.replicate m true) outer d) (port 6) _=_
      rw [store_update_inner]
      simp [s₁,s₂,store,port,List.replicate_succ]
    rwa [he] at hh
  obtain ⟨c,hc,hcb⟩ := inner_loop B g n m C states hB i 0 (m+1) hi (by omega) outer
  have h₃ := whilePop_executes _ _ _ g hc
  refine ⟨(5*m+2)+(1+c+2)+2,?_,by omega⟩
  simpa only [Nat.zero_add] using seq_executes _ _ g h₁ (seq_executes _ _ g h₂ h₃)

theorem cell_queryFree (B : OracleBlock (k+8)) (hB : B.QueryFree) : (cellBlock B).QueryFree :=
  seq_queryFree _ _ hB (advance_queryFree _ _)
theorem inner_queryFree (B : OracleBlock (k+8)) (hB : B.QueryFree) : (innerBlock B).QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (push_queryFree _ _)
    (whilePop_queryFree _ _ _ (cell_queryFree B hB) (cell_queryFree B hB)))
end HiddenCircuits.Complexity.GridRuntime
