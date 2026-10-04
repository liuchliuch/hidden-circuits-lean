import HiddenCircuits.Complexity.BinaryArithmetic.StraightLine
import HiddenCircuits.Complexity.OracleMove

/-! Fresh reconstruction: five actual integer multiplications, result movement,
and complete cleanup of the sixteen physical ratio-combination ports. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.RatioCombine
open Complexity OracleBlock BinaryArithmetic BinaryArithmetic.RegisterMachine Polynomial
set_option maxHeartbeats 700000

def registers (sign answer nt ns dt ds norm : ℤ) : Fin 7 → ℤ := ![sign,answer,nt,ns,dt,ds,norm]
def code : List Instruction := [⟨.multiply,0,0,1⟩,⟨.multiply,0,0,2⟩,⟨.multiply,0,0,3⟩,
  ⟨.multiply,4,4,5⟩,⟨.multiply,4,4,6⟩]
noncomputable def finish : OracleBlock 15 :=
  seq (moveOn 9 0 2 (by decide) (by decide) (by decide))
    (seq (moveOn 13 1 2 (by decide) (by decide) (by decide)) (clearList [9,10,11,12,13,14,15]))
noncomputable def program : OracleBlock 15 := seq (compile code) finish
noncomputable def time : Polynomial ℕ := straightTime code+20*(X+straightTime code)+100

lemma code_valid (R : Fin 7 → ℤ) : Valid code R := by simp [code,Valid,Operation.Valid]
lemma evaluate_code (sign answer nt ns dt ds norm : ℤ) :
    evaluate code (registers sign answer nt ns dt ds norm)=
      registers (sign*answer*nt*ns) answer nt ns (dt*ds*norm) ds norm := by
  funext i;fin_cases i <;> simp [code,evaluate,Instruction.eval,Operation.eval,registers,Function.update_apply]

lemma initial_bound (R : Fin 7 → ℤ) (B : ℕ) (h : Bounded B R) :
    ∀i,(store [] [] (signedBits ∘ R) i).length ≤ B := by
  intro i
  by_cases hi : 9 ≤ i.val
  · simpa [store,show i.val≠0 by omega,show i.val≠1 by omega,hi,Function.comp_def] using h ⟨i.val-9,by omega⟩
  · simp [store,hi]

lemma finish_executes (g : BitString → ℕ) (R : Fin 7 → ℤ) (M : ℕ)
    (h : ∀i,(store [] [] (signedBits ∘ R) i).length ≤ M) :
    ∃c,finish.Executes g (store [] [] (signedBits ∘ R))
      (store (signedBits (R 0)) (signedBits (R 4)) (fun _ => [])) c ∧ c ≤ 19*M+36 := by
  let s₁ := store [] [] (signedBits ∘ R)
  let s₂ := Function.update (Function.update s₁ (0:Fin 16) (signedBits (R 0))) 9 []
  let s₃ := Function.update (Function.update s₂ (1:Fin 16) (signedBits (R 4))) 13 []
  have h0 : s₁ 9=signedBits (R 0) := rfl
  have h4 : s₁ 13=signedBits (R 4) := rfl
  have hn : (signedBits (R 0)).length ≤ M := by simpa only [h0] using h 9
  have hd : (signedBits (R 4)).length ≤ M := by simpa only [h4] using h 13
  have h1 : (moveOn (9:Fin 16) 0 2 (by decide) (by decide) (by decide)).Executes g s₁ s₂
      (6*(signedBits (R 0)).length+5) := by
    simpa [s₂,s₁,store,Function.comp_def] using moveOn_executes g (9:Fin 16) 0 2 (by decide) (by decide) (by decide) s₁ rfl
  have h2 : (moveOn (13:Fin 16) 1 2 (by decide) (by decide) (by decide)).Executes g s₂ s₃
      (6*(signedBits (R 4)).length+5) := by
    simpa [s₃,s₂,s₁,store,Function.comp_def] using moveOn_executes g (13:Fin 16) 1 2 (by decide) (by decide) (by decide) s₂ rfl
  have hs : ∀i,(s₃ i).length ≤ M := by
    intro i
    by_cases h13 : i=13
    · subst i;simp [s₃]
    by_cases h1 : i=1
    · subst i;simpa [s₃] using hd
    by_cases h9 : i=9
    · subst i;simp [s₃,s₂]
    by_cases h0 : i=0
    · subst i;simpa [s₃,s₂] using hn
    simpa [s₃,s₂,Function.update_of_ne,h13,h1,h9,h0] using h i
  obtain ⟨c,hc,hcb⟩ := clearList_executes g ([9,10,11,12,13,14,15]:List (Fin 16)) s₃ M hs
  have he : eraseStore ([9,10,11,12,13,14,15]:List (Fin 16)) s₃=
      store (signedBits (R 0)) (signedBits (R 4)) (fun _ => []) := by
    funext i;fin_cases i <;> simp [eraseStore,s₃,s₂,s₁,store]
  rw [he] at hc
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 hc),?_⟩
  simp only [List.length_cons,List.length_nil] at hcb
  omega

theorem program_executes (g : BitString → ℕ) (sign answer nt ns dt ds norm : ℤ) (B : ℕ)
    (hB : Bounded B (registers sign answer nt ns dt ds norm)) :
    ∃c,program.Executes g (store [] [] (signedBits ∘ registers sign answer nt ns dt ds norm))
      (store (signedBits (sign*answer*nt*ns)) (signedBits (dt*ds*norm)) (fun _ => [])) c ∧ c ≤ time.eval B := by
  let R := registers sign answer nt ns dt ds norm
  obtain ⟨a,ha,hab⟩ := compile_polynomial code g R B hB (code_valid R)
  have hs := ha.stack_bound (initial_bound R B hB)
  obtain ⟨b,hb,hbb⟩ := finish_executes g (evaluate code R) (B+a) hs
  refine ⟨a+b+2,?_,?_⟩
  · have hh := seq_executes _ _ g ha hb
    simpa only [R,evaluate_code,registers,Matrix.cons_val_zero,Matrix.cons_val_succ] using hh
  · simp only [time,eval_add,eval_mul,eval_X,eval_ofNat]
    omega

lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (compile_queryFree code)
  (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _)
    (clearList_queryFree _)))
end HiddenCircuits.GraphReduction.Runtime.WordGraph.RatioCombine
