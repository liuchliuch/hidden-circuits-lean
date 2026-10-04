import HiddenCircuits.DH.Runtime.UnaryFor

/-! Fresh reconstruction: inclusive interpolation loops with complementary unary
indices. Every iteration is charged and invokes an actual body execution. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.ComplementFor
open Complexity OracleBlock DH.Runtime.UnaryFor
/-- A changing semantic state and invariant can be carried through the literal
pop/body/increment loop, including all five control instructions per iteration. -/
theorem executes {k : ℕ} {D : Type*} (clock index : Fin (k+1)) (B : OracleBlock k)
    (g : BitString→ℕ) (step : ℕ→D→D) (state : ℕ→ℕ→D→Store k) (Inv : ℕ→D→Prop) (bound limit : ℕ)
    (hclock : ∀i m d, state i m d clock=List.replicate m true)
    (hpop : ∀i m d, Function.update (state i (m+1) d) clock (List.replicate m true)=state i m d)
    (hinc : ∀i m d, Function.update (state i m d) index (true::state i m d index)=state (i+1) m d)
    (hbody : ∀i m d, Inv i d → i+m+1=limit → ∃cost, B.Executes g (state i m d) (state i m (step i d)) cost ∧
      cost≤bound ∧ Inv (i+1) (step i d))
    (i m : ℕ) (d : D) (hd : Inv i d) (hlimit : i+m=limit) :
    ∃cost, (HiddenCircuits.DH.Runtime.UnaryFor.program clock index B).Executes g (state i m d)
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

end HiddenCircuits.GraphReduction.Runtime.WordGraph.ComplementFor
