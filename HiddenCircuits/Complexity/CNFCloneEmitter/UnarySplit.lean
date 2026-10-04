import HiddenCircuits.Complexity.OracleStructured
import HiddenCircuits.Complexity.OracleLibrary
import HiddenCircuits.Complexity.OracleBlockNoQuery

/-! Actual consuming unary subtraction and strict comparison. It is used to
classify a clone vertex's side without assuming any arithmetic operation cost. -/
namespace HiddenCircuits.Complexity.CNFCloneEmitter.UnarySplit
open OracleBlock

def store (dividend subtrahend flag : BitString) : Store 2 := fun i =>
  if i.val=0 then dividend else if i.val=1 then subtrahend else flag
noncomputable def setTrue : OracleBlock 2 := seq (clear 2) (push 2 true)
noncomputable def body : OracleBlock 2 := branchPop 0 setTrue skip skip
noncomputable def loop : OracleBlock 2 := whilePop 1 body body
noncomputable def program : OracleBlock 2 := seq (push 2 false) loop

theorem setTrue_executes (g : BitString → ℕ) (y : ℕ) (b : Bool) :
    setTrue.Executes g (store [] (List.replicate y true) [b]) (store [] (List.replicate y true) [true]) 5 := by
  have hc := clear_executes g (2 : Fin 3) (store [] (List.replicate y true) [b])
  have hp := push_executes g (2 : Fin 3) true (Function.update (store [] (List.replicate y true) [b]) 2 [])
  convert seq_executes _ _ g hc hp using 1
  funext i;fin_cases i <;> simp [store]

theorem body_zero (g : BitString → ℕ) (y : ℕ) (b : Bool) :
    body.Executes g (store [] (List.replicate y true) [b]) (store [] (List.replicate y true) [true]) 7 :=
  branchPop_empty 0 setTrue skip skip g rfl (by simpa using setTrue_executes g y b)

theorem body_succ (g : BitString → ℕ) (x y : ℕ) (b : Bool) :
    body.Executes g (store (List.replicate (x+1) true) (List.replicate y true) [b])
      (store (List.replicate x true) (List.replicate y true) [b]) 3 := by
  apply branchPop_true _ _ _ _ g rfl
  have he : Function.update (store (List.replicate (x+1) true) (List.replicate y true) [b]) 0 (List.replicate x true)=
      store (List.replicate x true) (List.replicate y true) [b] := by
    funext i;fin_cases i <;> rfl
  rw [he]
  exact skip_executes _ _

lemma pop_clock (x y : ℕ) (b : Bool) :
    Function.update (store (List.replicate x true) (List.replicate (y+1) true) [b]) 1 (List.replicate y true)=
      store (List.replicate x true) (List.replicate y true) [b] := by
  funext i;fin_cases i <;> rfl

theorem loop_execution (g : BitString → ℕ) (x y : ℕ) (b : Bool) :
    ∃ cost, WhileExecution (1 : Fin 3) body body g
      (store (List.replicate x true) (List.replicate y true) [b])
      (store (List.replicate (x-y) true) [] [b || decide (x<y)]) cost ∧ cost≤9*y+1 := by
  induction y generalizing x b with
  | zero => exact ⟨1,by simpa using WhileExecution.empty (store (List.replicate x true) [] [b]) rfl,by simp⟩
  | succ y ih =>
    cases x with
    | zero =>
      obtain ⟨ct,ht,hbt⟩ := ih 0 true
      have hb := body_zero g y b
      have h := WhileExecution.one (stack:=(1:Fin 3)) (B:=body) (C:=body) (g:=g)
        (show store [] (List.replicate (y+1) true) [b] 1=true::List.replicate y true from rfl)
        (by
          have he : Function.update (store [] (List.replicate (y+1) true) [b]) 1 (List.replicate y true)=
              store [] (List.replicate y true) [b] := by funext i;fin_cases i <;> rfl
          rw [he];exact hb) ht
      exact ⟨1+7+1+ct,by simpa using h,by omega⟩
    | succ x =>
      obtain ⟨ct,ht,hbt⟩ := ih x b
      have hb := body_succ g x y b
      have h := WhileExecution.one (stack:=(1:Fin 3)) (B:=body) (C:=body) (g:=g)
        (show store (List.replicate (x+1) true) (List.replicate (y+1) true) [b] 1=true::List.replicate y true from rfl)
        (by rw [pop_clock];exact hb) ht
      exact ⟨1+3+1+ct,by simpa using h,by omega⟩

theorem program_executes (g : BitString → ℕ) (x y : ℕ) :
    ∃ cost, program.Executes g (store (List.replicate x true) (List.replicate y true) [])
      (store (List.replicate (x-y) true) [] [decide (x<y)]) cost ∧ cost≤9*y+4 := by
  have hp : (push (2 : Fin 3) false).Executes g
      (store (List.replicate x true) (List.replicate y true) [])
      (store (List.replicate x true) (List.replicate y true) [false]) 1 := by
    convert push_executes g (2 : Fin 3) false (store (List.replicate x true) (List.replicate y true) []) using 1
    funext i;fin_cases i <;> rfl
  obtain ⟨c,hc,hb⟩ := loop_execution g x y false
  refine ⟨1+c+2,?_,by omega⟩
  simpa only [Bool.false_or] using seq_executes _ _ g hp (whilePop_executes _ _ _ g hc)

lemma setTrue_queryFree : setTrue.QueryFree := seq_queryFree _ _ (clear_queryFree _) (push_queryFree _ _)
lemma body_queryFree : body.QueryFree := branchPop_queryFree _ _ _ _ setTrue_queryFree skip_queryFree skip_queryFree
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (push_queryFree _ _)
  (whilePop_queryFree _ _ _ body_queryFree body_queryFree)

noncomputable def on {k : ℕ} (φ : Fin 3 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 3 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k) (x y : ℕ)
    (hs : s ∘ φ=store (List.replicate x true) (List.replicate y true) []) :
    ∃ cost, (on φ).Executes g s
      (Function.update (Function.update (Function.update s (φ 0) (List.replicate (x-y) true)) (φ 1) []) (φ 2) [decide (x<y)]) cost ∧
      cost≤9*y+4 := by
  obtain ⟨c,hc,hb⟩ := program_executes g x y
  refine ⟨c,?_,hb⟩
  apply rename_executes_to _ φ g hc hs
  · funext i
    simp only [Function.comp_def] at *
    fin_cases i <;> simp [Function.update_apply,φ.injective.eq_iff,store]
  · intro i hi
    simp only [Function.update_of_ne (hi 0).symm,Function.update_of_ne (hi 1).symm,Function.update_of_ne (hi 2).symm]
lemma on_queryFree {k : ℕ} (φ : Fin 3 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ program_queryFree

end HiddenCircuits.Complexity.CNFCloneEmitter.UnarySplit
