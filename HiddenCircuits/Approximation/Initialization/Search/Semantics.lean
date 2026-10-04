import HiddenCircuits.Approximation.Initialization.Search.Program

/-! Operational correctness and explicit cost of the actual callback loop. -/
namespace HiddenCircuits.Approximation.Initialization.Search
open Complexity Complexity.OracleBlock
variable {k : ℕ}

theorem loop_while (B : OracleBlock (k+5)) (g : BitString → ℕ)
    (params : Store (k+5)) (n : ℕ) (f : ℕ → Bool) (T : ℕ)
    (hB : CallbackSpec B g params n f T) (i m : ℕ) (him : i+m≤n) :
    ∃ j t, WhileExecution (port 4) (body B) (body B) g
      (state params n i [] [] m)
      (state params n j [] (encodeOption ((List.range' i m).find? f)) 0) t ∧
      j≤n ∧ t≤m*(T+6*n+20)+1 := by
  induction m generalizing i with
  | zero =>
    refine ⟨i,1,?_,by omega,by simp⟩
    simpa [encodeOption] using WhileExecution.empty (stack:=port 4) (B:=body B) (C:=body B)
      (g:=g) (state params n i [] [] 0) rfl
  | succ m ih =>
    obtain ⟨t,ht,htb⟩ := hB i (by omega) m
    cases hf : f i with
    | false =>
      obtain ⟨j,c,hc,hjn,hcb⟩ := ih (i+1) (by omega)
      have hb := body_false B g params n i m t (by simpa [hf] using ht)
      have hb' : (body B).Executes g
          (Function.update (state params n i [] [] (m+1)) (port 4) (unary m))
          (state params n (i+1) [] [] m) (t+5) := by
        simpa only [update_clock] using hb
      have hh := WhileExecution.one (s:=state params n i [] [] (m+1))
        (show state params n i [] [] (m+1) (port 4)=true::unary m from rfl) hb' hc
      refine ⟨j,1+(t+5)+1+c,?_,hjn,?_⟩
      · simpa [List.range'_succ,List.find?_cons,hf] using hh
      · nlinarith
    | true =>
      have hb := body_true B g params n i m t (by simpa [hf] using ht)
      have hb' : (body B).Executes g
          (Function.update (state params n i [] [] (m+1)) (port 4) (unary m))
          (state params n i [] (encodeOption (some i)) 0) (t+5*i+m+12) := by
        simpa only [update_clock] using hb
      have he := WhileExecution.empty (stack:=port 4) (B:=body B) (C:=body B) (g:=g)
        (state params n i [] (encodeOption (some i)) 0) rfl
      have hh := WhileExecution.one (s:=state params n i [] [] (m+1))
        (show state params n i [] [] (m+1) (port 4)=true::unary m from rfl) hb' he
      refine ⟨i,1+(t+5*i+m+12)+1+1,?_,by omega,?_⟩
      · simpa [List.range'_succ,List.find?_cons,hf] using hh
      · have hmul : T+6*n+20≤(m+1)*(T+6*n+20) := by nlinarith
        nlinarith

/-- Find the least accepted candidate, or none, with clean control work tapes.
The bound includes every copy, branch, jump, pop and cleanup instruction. -/
theorem program_executes (B : OracleBlock (k+5)) (g : BitString → ℕ)
    (params : Store (k+5)) (n : ℕ) (f : ℕ → Bool) (T : ℕ)
    (hB : CallbackSpec B g params n f T) :
    ∃ t, (program B).Executes g (state params n 0 [] [] 0)
      (state params n 0 [] (encodeOption ((List.range n).find? f)) 0) t ∧ t≤timeBound n T := by
  have hi : (copyOn (port 0) (port 4) (port 5) (by simp [port]) (by simp [port]) (by simp [port])).Executes g
      (state params n 0 [] [] 0) (state params n 0 [] [] n) (5*n+2) := by
    simpa using copyOn_executes g (port 0) (port 4) (port 5)
      (by simp [port]) (by simp [port]) (by simp [port]) (state params n 0 [] [] 0) rfl
  obtain ⟨j,c,hc,hjn,hcb⟩ := loop_while B g params n f T hB 0 n (by omega)
  have hl : (loop B).Executes g (state params n 0 [] [] n)
      (state params n j [] (encodeOption ((List.range n).find? f)) 0) c := by
    simpa [loop,←List.range_eq_range'] using whilePop_executes _ _ _ g hc
  have hd : (clear (port 1)).Executes g
      (state params n j [] (encodeOption ((List.range n).find? f)) 0)
      (state params n 0 [] (encodeOption ((List.range n).find? f)) 0) (j+1) := by
    simpa only [state_port1,List.length_replicate,←show unary 0=[] from rfl,update_index]
      using clear_executes g (port 1) (state params n j [] (encodeOption ((List.range n).find? f)) 0)
  refine ⟨_,seq_executes _ _ g hi (seq_executes _ _ g hl hd),?_⟩
  unfold timeBound
  nlinarith

/-- On an empty candidate range the callback is never invoked; exact cost eight. -/
theorem program_empty (B : OracleBlock (k+5)) (g : BitString → ℕ) (params : Store (k+5)) :
    (program B).Executes g (state params 0 0 [] [] 0) (state params 0 0 [] [] 0) 8 := by
  have hi : (copyOn (port 0) (port 4) (port 5) (by simp [port]) (by simp [port]) (by simp [port])).Executes g
      (state params 0 0 [] [] 0) (state params 0 0 [] [] 0) 2 := by
    have he : Function.update (state params 0 0 [] [] 0) (port 4) []=state params 0 0 [] [] 0 :=
      update_clock params 0 0 [] [] 0 0
    simpa only [state_port0,state_port4,List.length_replicate,List.replicate_zero,List.nil_append,
      he,Nat.mul_zero,Nat.zero_add] using copyOn_executes g (port 0) (port 4) (port 5)
      (by simp [port]) (by simp [port]) (by simp [port]) (state params 0 0 [] [] 0) rfl
  have hl : (loop B).Executes g (state params 0 0 [] [] 0) (state params 0 0 [] [] 0) 1 :=
    whilePop_executes _ _ _ g (WhileExecution.empty _ rfl)
  have hd : (clear (port 1)).Executes g (state params 0 0 [] [] 0) (state params 0 0 [] [] 0) 1 := by
    simpa only [state_port1,List.length_replicate,←show unary 0=[] from rfl,update_index]
      using clear_executes g (port 1) (state params 0 0 [] [] 0)
  exact seq_executes _ _ g hi (seq_executes _ _ g hl hd)

end HiddenCircuits.Approximation.Initialization.Search
