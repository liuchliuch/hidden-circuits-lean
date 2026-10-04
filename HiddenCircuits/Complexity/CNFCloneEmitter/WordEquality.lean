import HiddenCircuits.Complexity.OracleStructured
import HiddenCircuits.Complexity.OracleLibrary
import HiddenCircuits.Complexity.OracleBlockNoQuery

/-! A finite clean destructive word comparator. Every bit comparison and scratch
update is performed by actual stack instructions, with a linear execution bound. -/
namespace HiddenCircuits.Complexity.CNFCloneEmitter.WordEquality
open OracleBlock

def store (xs ys : BitString) (flag : Bool) : Store 2 :=
  fun i => if i.val=0 then xs else if i.val=1 then ys else [flag]

noncomputable def setFalse : OracleBlock 2 := seq (clear 2) (push 2 false)
noncomputable def body (bit : Bool) : OracleBlock 2 :=
  branchPop 1 setFalse (if bit then setFalse else skip) (if bit then skip else setFalse)
noncomputable def loop : OracleBlock 2 := whilePop 0 (body false) (body true)
noncomputable def finish : OracleBlock 2 :=
  branchPop 1 skip (seq (clear 1) setFalse) (seq (clear 1) setFalse)
noncomputable def program : OracleBlock 2 := seq loop finish

def agree : BitString → BitString → Bool
  | [], _ => true
  | _::_, [] => false
  | x::xs, y::ys => (x==y) && agree xs ys

def remaining (xs ys : BitString) : BitString := ys.drop xs.length

lemma remaining_cons (x : Bool) (xs : BitString) (y : Bool) (ys : BitString) :
    remaining (x::xs) (y::ys)=remaining xs ys := rfl
lemma remaining_nil (xs : BitString) : remaining xs []=[] := by simp [remaining]
lemma remaining_length (xs ys : BitString) : (remaining xs ys).length≤ys.length := by simp [remaining]

lemma agree_empty (xs ys : BitString) :
    (agree xs ys && decide (remaining xs ys=[])) = decide (xs=ys) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [agree,remaining]
  | cons x xs ih =>
    cases ys with
    | nil => simp [agree]
    | cons y ys =>
      rw [agree,remaining_cons,Bool.and_assoc,ih]
      cases x <;> cases y <;> simp

theorem setFalse_executes (g : BitString → ℕ) (xs ys : BitString) (b : Bool) :
    setFalse.Executes g (store xs ys b) (store xs ys false) 5 := by
  have hc := clear_executes g (2 : Fin 3) (store xs ys b)
  have hp := push_executes g (2 : Fin 3) false (Function.update (store xs ys b) 2 [])
  convert seq_executes _ _ g hc hp using 1
  funext i;fin_cases i <;> simp [store]

lemma pop_right (xs ys : BitString) (bit b : Bool) :
    Function.update (store xs (bit::ys) b) 1 ys=store xs ys b := by
  funext i;fin_cases i <;> rfl
lemma pop_left (xs ys : BitString) (bit b : Bool) :
    Function.update (store (bit::xs) ys b) 0 xs=store xs ys b := by
  funext i;fin_cases i <;> rfl

theorem body_nil (g : BitString → ℕ) (x b : Bool) (xs : BitString) :
    (body x).Executes g (store xs [] b) (store xs [] false) 7 := by
  exact branchPop_empty 1 setFalse _ _ g rfl (by
    simpa only [Function.update_eq_self] using setFalse_executes g xs [] b)

theorem body_cons (g : BitString → ℕ) (x y b : Bool) (xs ys : BitString) :
    ∃ cost, (body x).Executes g (store xs (y::ys) b) (store xs ys (b && (x==y))) cost ∧ cost≤7 := by
  cases x <;> cases y
  · refine ⟨3,?_,by omega⟩
    apply branchPop_false _ _ _ _ g rfl
    simpa [pop_right] using skip_executes g (store xs ys b)
  · refine ⟨7,?_,by omega⟩
    apply branchPop_true _ _ _ _ g rfl
    simpa [pop_right] using setFalse_executes g xs ys b
  · refine ⟨7,?_,by omega⟩
    apply branchPop_false _ _ _ _ g rfl
    simpa [pop_right] using setFalse_executes g xs ys b
  · refine ⟨3,?_,by omega⟩
    apply branchPop_true _ _ _ _ g rfl
    simpa [pop_right] using skip_executes g (store xs ys b)

theorem loop_execution (g : BitString → ℕ) (xs ys : BitString) (b : Bool) :
    ∃ cost, WhileExecution (0 : Fin 3) (body false) (body true) g (store xs ys b)
      (store [] (remaining xs ys) (b && agree xs ys)) cost ∧ cost≤9*xs.length+1 := by
  induction xs generalizing ys b with
  | nil => exact ⟨1,by simpa [remaining,agree] using WhileExecution.empty (store [] ys b) rfl,by simp⟩
  | cons x xs ih =>
    cases ys with
    | nil =>
      obtain ⟨ct,ht,hbt⟩ := ih [] false
      have hb : (body x).Executes g (Function.update (store (x::xs) [] b) 0 xs) (store xs [] false) 7 := by
        rw [pop_left];exact body_nil g x b xs
      have he : (store (x::xs) [] b) 0=x::xs := rfl
      have h : WhileExecution (0 : Fin 3) (body false) (body true) g (store (x::xs) [] b)
          (store [] [] false) (1+7+1+ct) := by
        simp only [remaining_nil,Bool.false_and] at ht
        cases x
        · exact WhileExecution.zero he hb ht
        · exact WhileExecution.one he hb ht
      exact ⟨_,by simpa [agree,remaining_nil] using h,by simp only [List.length_cons];omega⟩
    | cons y ys =>
      obtain ⟨cb,hb,hbb⟩ := body_cons g x y b xs ys
      obtain ⟨ct,ht,hbt⟩ := ih ys (b && (x==y))
      have hb' : (body x).Executes g (Function.update (store (x::xs) (y::ys) b) 0 xs)
          (store xs ys (b && (x==y))) cb := by rwa [pop_left]
      have he : (store (x::xs) (y::ys) b) 0=x::xs := rfl
      have h : WhileExecution (0 : Fin 3) (body false) (body true) g (store (x::xs) (y::ys) b)
          (store [] (remaining xs ys) ((b && (x==y)) && agree xs ys)) (1+cb+1+ct) := by
        cases x
        · exact WhileExecution.zero he hb' ht
        · exact WhileExecution.one he hb' ht
      exact ⟨_,by simpa [agree,remaining_cons,Bool.and_assoc] using h,by simp only [List.length_cons];omega⟩

theorem finish_executes (g : BitString → ℕ) (ys : BitString) (b : Bool) :
    ∃ cost, finish.Executes g (store [] ys b) (store [] [] (b && decide (ys=[]))) cost ∧ cost≤ys.length+10 := by
  cases ys with
  | nil =>
    refine ⟨3,?_,by simp⟩
    apply branchPop_empty _ _ _ _ g rfl
    simpa using skip_executes g (store [] [] b)
  | cons y ys =>
    have hc : (clear (1 : Fin 3)).Executes g (store [] ys b) (store [] [] b) (ys.length+1) := by
      convert clear_executes g (1 : Fin 3) (store [] ys b) using 1
      funext i;fin_cases i <;> simp [store]
    have hb := seq_executes _ _ g hc (setFalse_executes g [] [] b)
    have hb' : (seq (clear (1 : Fin 3)) setFalse).Executes g
        (Function.update (store [] (y::ys) b) 1 ys) (store [] [] false) (ys.length+1+5+2) := by
      rwa [pop_right]
    refine ⟨ys.length+1+5+2+2,?_,by simp⟩
    cases y
    · simpa using branchPop_false 1 skip (seq (clear 1) setFalse) (seq (clear 1) setFalse) g rfl hb'
    · simpa using branchPop_true 1 skip (seq (clear 1) setFalse) (seq (clear 1) setFalse) g rfl hb'

/-- Clean exact equality of arbitrary finite bit words; the singleton input flag
is true, and all operand stacks are physically emptied on exit. -/
theorem program_executes (g : BitString → ℕ) (xs ys : BitString) :
    ∃ cost, program.Executes g (store xs ys true) (store [] [] (decide (xs=ys))) cost ∧
      cost≤10*(xs.length+ys.length)+13 := by
  obtain ⟨cl,hl,hbl⟩ := loop_execution g xs ys true
  obtain ⟨cf,hf,hbf⟩ := finish_executes g (remaining xs ys) (true && agree xs ys)
  have hr := seq_executes _ _ g (whilePop_executes _ _ _ g hl) hf
  refine ⟨cl+cf+2,?_,?_⟩
  · simpa only [Bool.true_and,agree_empty] using hr
  · have hlen := remaining_length xs ys;omega

lemma setFalse_queryFree : setFalse.QueryFree := seq_queryFree _ _ (clear_queryFree _) (push_queryFree _ _)
lemma body_queryFree (b : Bool) : (body b).QueryFree := by
  cases b <;> exact branchPop_queryFree _ _ _ _ setFalse_queryFree (by first | exact skip_queryFree | exact setFalse_queryFree)
    (by first | exact skip_queryFree | exact setFalse_queryFree)
lemma finish_queryFree : finish.QueryFree := branchPop_queryFree _ _ _ _ skip_queryFree
  (seq_queryFree _ _ (clear_queryFree _) setFalse_queryFree) (seq_queryFree _ _ (clear_queryFree _) setFalse_queryFree)
lemma program_queryFree : program.QueryFree := seq_queryFree _ _
  (whilePop_queryFree _ _ _ (body_queryFree _) (body_queryFree _)) finish_queryFree

end HiddenCircuits.Complexity.CNFCloneEmitter.WordEquality
