import HiddenCircuits.Complexity.OracleRepeat

/-! Compositional verification of actual unary-index for loops. The loop body
is a fixed finite block, and every use must supply its real Executes theorem. -/
namespace HiddenCircuits.DH.Runtime.UnaryFor
open Complexity Complexity.OracleBlock

 noncomputable def body {k : ℕ} (index : Fin (k+1)) (B : OracleBlock k) : OracleBlock k := seq B (push index true)
 noncomputable def program {k : ℕ} (clock index : Fin (k+1)) (B : OracleBlock k) : OracleBlock k :=
  whilePop clock (body index B) (body index B)

 def iterate {D : Type*} (step : ℕ→D→D) : ℕ→ℕ→D→D
  | _,0,d => d
  | i,m+1,d => iterate step (i+1) m (step i d)

/-- A changing semantic state and invariant can be carried through the literal
pop/body/increment loop, including all five control instructions per iteration. -/
theorem executes {k : ℕ} {D : Type*} (clock index : Fin (k+1)) (B : OracleBlock k)
    (g : BitString→ℕ) (step : ℕ→D→D) (state : ℕ→ℕ→D→Store k) (Inv : ℕ→D→Prop) (bound limit : ℕ)
    (hclock : ∀i m d, state i m d clock=List.replicate m true)
    (hpop : ∀i m d, Function.update (state i (m+1) d) clock (List.replicate m true)=state i m d)
    (hinc : ∀i m d, Function.update (state i m d) index (true::state i m d index)=state (i+1) m d)
    (hbody : ∀i m d, Inv i d → i<limit → ∃cost, B.Executes g (state i m d) (state i m (step i d)) cost ∧
      cost≤bound ∧ Inv (i+1) (step i d))
    (i m : ℕ) (d : D) (hd : Inv i d) (hlimit : i+m≤limit) :
    ∃cost, (program clock index B).Executes g (state i m d)
      (state (i+m) 0 (iterate step i m d)) cost ∧ cost≤m*(bound+5)+1 ∧ Inv (i+m) (iterate step i m d) := by
  suffices h : ∃cost, WhileExecution clock (body index B) (body index B) g (state i m d)
      (state (i+m) 0 (iterate step i m d)) cost ∧ cost≤m*(bound+5)+1 ∧ Inv (i+m) (iterate step i m d) by
    obtain ⟨cost,hc,hb,hi⟩ := h
    exact ⟨cost,whilePop_executes _ _ _ g hc,hb,hi⟩
  induction m generalizing i d with
  | zero =>
    refine ⟨1,?_,by simp,?_⟩
    · simpa only [Nat.add_zero,iterate] using (WhileExecution.empty (state i 0 d) (hclock i 0 d))
    · simpa only [Nat.add_zero,iterate] using hd
  | succ m ih =>
    obtain ⟨c,hc,hcb,hid⟩ := hbody i m d hd (by omega)
    have hp : (push index true).Executes g (state i m (step i d)) (state (i+1) m (step i d)) 1 := by
      rw [←hinc]
      exact push_executes g index true (state i m (step i d))
    have hb : (body index B).Executes g
        (Function.update (state i (m+1) d) clock (List.replicate m true)) (state (i+1) m (step i d)) (c+1+2) := by
      rw [hpop]
      exact seq_executes _ _ g hc hp
    obtain ⟨t,ht,htb,hti⟩ := ih (i+1) (step i d) hid (by omega)
    have hall := WhileExecution.one (by simpa using hclock i (m+1) d) hb ht
    refine ⟨1+(c+1+2)+1+t,?_,?_,?_⟩
    · simpa only [iterate,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hall
    · nlinarith
    · simpa only [iterate,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hti

lemma queryFree {k : ℕ} (clock index : Fin (k+1)) (B : OracleBlock k) (h : B.QueryFree) :
    (program clock index B).QueryFree :=
  whilePop_queryFree _ _ _ (seq_queryFree _ _ h (push_queryFree _ _)) (seq_queryFree _ _ h (push_queryFree _ _))

end HiddenCircuits.DH.Runtime.UnaryFor
