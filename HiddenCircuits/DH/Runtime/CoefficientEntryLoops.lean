import HiddenCircuits.DH.Runtime.CoefficientEntryCore

/-! The innermost and middle clocks are physically
copied and popped; every accumulator state is the exact finite-sum prefix. -/
namespace HiddenCircuits.DH.Runtime.CoefficientEntry
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic PruningModel CoefficientRow
open UniformCoefficientModel Polynomial
set_option maxHeartbeats 1800000

noncomputable def rLoop (kind : Kind) : OracleBlock 35:=whilePop 9 (cell kind) (cell kind)
noncomputable def rowBody (kind : Kind) : OracleBlock 35:=seq (copyOn 0 9 13 (by decide) (by decide) (by decide))
  (seq (push 9 true) (seq (rLoop kind) (seq (clear 8) (push 7 true))))
noncomputable def rowLoop (kind : Kind) : OracleBlock 35:=whilePop 10 (rowBody kind) (rowBody kind)
noncomputable def rowTime : Polynomial ℕ:=(X+1)*(cellTime+2)+6*X+20

lemma pop_rclock (kind : Kind) (left right : List ℕ) (a b k i j r ci cj m : ℕ) :
    Function.update (prefixState kind left right a b k i j r ci cj (m+1)) 9 (List.replicate m true)=
      prefixState kind left right a b k i j r ci cj m:=by
  funext q;fin_cases q <;> rfl
lemma rLoop_execution (g : BitString→ ℕ) (n : ℕ) (kind : Kind) (left right : List ℕ) (a b k i j ci cj : ℕ)
    (ha:a≤ n) (hb:b≤ n) (hk:k≤ n) (hl:left.length=n+1) (hr:right.length=n+1) (hi:i≤ a) (hj:j≤ b)
    (r m : ℕ) (hm:r+m≤ a+1) :
    ∃t,WhileExecution (9:Fin 36) (cell kind) (cell kind) g
      (prefixState kind left right a b k i j r ci cj m)
      (prefixState kind left right a b k i j (r+m) ci cj 0) t ∧
      t≤ m*(cellTime.eval (inputSize n left right)+2)+1 := by
  induction m generalizing r with
  | zero=>exact ⟨1,by simpa only [Nat.add_zero] using WhileExecution.empty (prefixState kind left right a b k i j r ci cj 0) rfl,by simp⟩
  | succ m ih=>
    obtain ⟨c,hc,hcb⟩:=cell_executes g n kind left right a b k i j r ci cj m ha hb hk hl hr hi hj (by omega)
    obtain ⟨t,ht,htb⟩:=ih (r+1) (by omega)
    have h:=WhileExecution.one (show prefixState kind left right a b k i j r ci cj (m+1) 9=true::List.replicate m true from rfl)
      (by rw [pop_rclock];exact hc) ht
    refine ⟨1+c+1+t,?_,by nlinarith⟩
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

lemma rowBody_executes (g : BitString→ ℕ) (n : ℕ) (kind : Kind) (left right : List ℕ) (a b k i j ci cj : ℕ)
    (ha:a≤ n) (hb:b≤ n) (hk:k≤ n) (hl:left.length=n+1) (hr:right.length=n+1) (hi:i≤ a) (hj:j≤ b) :
    ∃t,(rowBody kind).Executes g (prefixState kind left right a b k i j 0 ci cj 0)
      (prefixState kind left right a b k i (j+1) 0 ci cj 0) t ∧ t≤ rowTime.eval (inputSize n left right) := by
  have hc:(copyOn (0:Fin 36) 9 13 (by decide) (by decide) (by decide)).Executes g
      (prefixState kind left right a b k i j 0 ci cj 0) (prefixState kind left right a b k i j 0 ci cj a) (5*a+2):=by
    convert copyOn_executes g (0:Fin 36) 9 13 (by decide) (by decide) (by decide)
      (prefixState kind left right a b k i j 0 ci cj 0) rfl using 1
    · funext q;fin_cases q <;> simp [prefixState,state]
    · simp [prefixState,state]
  have hp:(push (9:Fin 36) true).Executes g (prefixState kind left right a b k i j 0 ci cj a)
      (prefixState kind left right a b k i j 0 ci cj (a+1)) 1:=by
    convert push_executes g (9:Fin 36) true (prefixState kind left right a b k i j 0 ci cj a) using 1
    funext q;fin_cases q <;> rfl
  obtain ⟨c,hc',hcb⟩:=rLoop_execution g n kind left right a b k i j ci cj ha hb hk hl hr hi hj 0 (a+1) (by omega)
  have hs:(rLoop kind).Executes g (prefixState kind left right a b k i j 0 ci cj (a+1))
      (prefixState kind left right a b k i j (a+1) ci cj 0) c:=by
    simpa only [Nat.zero_add] using whilePop_executes _ _ _ g hc'
  let mid:=state left right a b k i j 0 ci cj 0 (signedBits (prefixValue kind a b left right k i (j+1) 0:ℕ)) []
  have hd:(clear (8:Fin 36)).Executes g (prefixState kind left right a b k i j (a+1) ci cj 0) mid (a+2):=by
    convert clear_executes g (8:Fin 36) (prefixState kind left right a b k i j (a+1) ci cj 0) using 1
    · funext q;fin_cases q <;> simp [prefixState,state,mid,prefix_row]
    · simp [prefixState,state] <;> omega
  have hi':(push (7:Fin 36) true).Executes g mid (prefixState kind left right a b k i (j+1) 0 ci cj 0) 1:=by
    convert push_executes g (7:Fin 36) true mid using 1
    funext q;fin_cases q <;> rfl
  refine ⟨_,seq_executes _ _ g hc (seq_executes _ _ g hp (seq_executes _ _ g hs (seq_executes _ _ g hd hi'))),?_⟩
  have hN:n≤ inputSize n left right:=by unfold inputSize;omega
  have hm:(a+1)*(cellTime.eval (inputSize n left right)+2)≤(inputSize n left right+1)*(cellTime.eval (inputSize n left right)+2):=
    Nat.mul_le_mul_right _ (by omega)
  simp only [rowTime,eval_add,eval_mul,eval_X,eval_ofNat,eval_one]
  omega

lemma pop_jclock (kind : Kind) (left right : List ℕ) (a b k i j ci m : ℕ) :
    Function.update (prefixState kind left right a b k i j 0 ci (m+1) 0) 10 (List.replicate m true)=
      prefixState kind left right a b k i j 0 ci m 0:=by
  funext q;fin_cases q <;> rfl
lemma rowLoop_execution (g : BitString→ ℕ) (n : ℕ) (kind : Kind) (left right : List ℕ) (a b k i ci : ℕ)
    (ha:a≤ n) (hb:b≤ n) (hk:k≤ n) (hl:left.length=n+1) (hr:right.length=n+1) (hi:i≤ a)
    (j m : ℕ) (hm:j+m≤ b+1) :
    ∃t,WhileExecution (10:Fin 36) (rowBody kind) (rowBody kind) g
      (prefixState kind left right a b k i j 0 ci m 0)
      (prefixState kind left right a b k i (j+m) 0 ci 0 0) t ∧
      t≤ m*(rowTime.eval (inputSize n left right)+2)+1 := by
  induction m generalizing j with
  | zero=>exact ⟨1,by simpa only [Nat.add_zero] using WhileExecution.empty (prefixState kind left right a b k i j 0 ci 0 0) rfl,by simp⟩
  | succ m ih=>
    obtain ⟨c,hc,hcb⟩:=rowBody_executes g n kind left right a b k i j ci m ha hb hk hl hr hi (by omega)
    obtain ⟨t,ht,htb⟩:=ih (j+1) (by omega)
    have h:=WhileExecution.one (show prefixState kind left right a b k i j 0 ci (m+1) 0 10=true::List.replicate m true from rfl)
      (by rw [pop_jclock];exact hc) ht
    refine ⟨1+c+1+t,?_,by nlinarith⟩
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
lemma rLoop_queryFree (kind : Kind) : (rLoop kind).QueryFree:=whilePop_queryFree _ _ _ (cell_queryFree kind) (cell_queryFree kind)
lemma rowBody_queryFree (kind : Kind) : (rowBody kind).QueryFree:=seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (push_queryFree _ _) (seq_queryFree _ _ (rLoop_queryFree kind)
    (seq_queryFree _ _ (clear_queryFree _) (push_queryFree _ _))))
lemma rowLoop_queryFree (kind : Kind) : (rowLoop kind).QueryFree:=whilePop_queryFree _ _ _ (rowBody_queryFree kind) (rowBody_queryFree kind)
end HiddenCircuits.DH.Runtime.CoefficientEntry
