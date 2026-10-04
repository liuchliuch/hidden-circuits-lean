import HiddenCircuits.GraphReduction.Runtime.UnitOrderRootsLoop
import HiddenCircuits.GraphReduction.Runtime.UnitOrderSemantics
import HiddenCircuits.Complexity.OracleMove

/-! Literal residual rounds with a saved reversed component array and a global
array of original vertex labels. Failed root searches stutter exactly. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitOrderRounds
open Complexity Complexity.OracleBlock DH.Runtime.PairCheck

abbrev run := @UnitOrderSemantics.run

def labelBits {n : ℕ} (ls : List (Fin n)) : BitString :=
  encodeBitList (ls.map (fun v => List.replicate v.val true))
lemma labelBits_append {n : ℕ} (ls rs : List (Fin n)) :
    labelBits (ls++rs)=labelBits ls++labelBits rs := by
  simp [labelBits,List.map_append,BinaryArithmetic.encodeBitList_append]
lemma savedBits_eq {n : ℕ} (G : MatrixData n) (A : Vector Bool n) (b : UnitOrderRoots.Best n) :
    UnitOrderRoots.savedBits G A b=labelBits (UnitOrderSemantics.savedOrder G A b) := by
  cases b <;> simp [UnitOrderRoots.savedBits,UnitOrderSemantics.savedOrder,
    labelBits,UnitRecognitionComponent.orderBits,encodeBitList]

def state {n : ℕ} (G : MatrixData n) (A : Vector Bool n) (acc : List (Fin n)) (clock : BitString) : Store 45 := fun r=>
  if r.val=0 then List.replicate n true else if r.val=1 then G.bits
  else if r.val=2 then liveBits A else if r.val=44 then clock else if r.val=45 then labelBits acc else []
def rootState {n : ℕ} (G : MatrixData n) (A : Vector Bool n) (b : UnitOrderRoots.Best n)
    (acc : List (Fin n)) (clock : BitString) : Store 45 := fun r=>
  if h:r.val<44 then UnitOrderRoots.state G A b 0 none [] [] [] [] [] [] ⟨r.val,h⟩
  else if r.val=44 then clock else labelBits acc

def rootsEmbedding : Fin 44 ↪ Fin 46 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun z : Fin 46=>z.val) h)
noncomputable def setup : OracleBlock 45 := seq
  (copyOn 2 37 15 (by decide) (by decide) (by decide)) (seq (push 38 false) (push 8 false))
noncomputable def roots : OracleBlock 45 := rename UnitOrderRoots.program rootsEmbedding
noncomputable def finish : OracleBlock 45 := seq (clear 2)
  (seq (moveOn 37 2 15 (by decide) (by decide) (by decide))
    (seq (clear 38) (seq (clear 8) (moveOn 43 45 15 (by decide) (by decide) (by decide)))))
noncomputable def body : OracleBlock 45 := seq setup (seq roots finish)

theorem setup_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n) (A : Vector Bool n)
    (acc : List (Fin n)) (clock : BitString) :
    setup.Executes g (state G A acc clock) (rootState G A none acc clock) (20*n+8) := by
  have h1 := copyOn_executes g (2 : Fin 46) 37 15 (by decide) (by decide) (by decide) (state G A acc clock) rfl
  have h2 := push_executes g (38 : Fin 46) false (Function.update (state G A acc clock) 37 ((state G A acc clock) 2++(state G A acc clock) 37))
  have h3 := push_executes g (8 : Fin 46) false
    (Function.update (Function.update (state G A acc clock) 37 ((state G A acc clock) 2++(state G A acc clock) 37)) 38
      (false::(Function.update (state G A acc clock) 37 ((state G A acc clock) 2++(state G A acc clock) 37)) 38))
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 h3) using 1
  · funext i;fin_cases i <;> simp [state,rootState,UnitOrderRoots.state,UnitOrderRoots.residual,
      UnitRecognitionRoots.residual,UnitOrderRoots.savedBits,UnitRecognitionComponent.store,UnitRecognitionChoice.rawState]
  · simp [state,liveBits_length];ring

theorem roots_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n) (A : Vector Bool n)
    (acc : List (Fin n)) (clock : BitString) :
    ∃t, roots.Executes g (rootState G A none acc clock) (rootState G A (UnitOrderRoots.find G A) acc clock) t ∧
      t≤12000*(n+1)^6 := by
  obtain ⟨t,ht,hb⟩ := UnitOrderRoots.program_executes g G A
  refine ⟨t,?_,hb⟩
  apply rename_executes_to UnitOrderRoots.program rootsEmbedding g ht
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have h : ¬i.val<44 := by intro hh;exact hi ⟨i.val,hh⟩ (Fin.ext rfl)
    simp [rootState,h]

theorem finish_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n) (A : Vector Bool n)
    (b : UnitOrderRoots.Best n) (acc : List (Fin n)) (clock : BitString) :
    ∃t, finish.Executes g (rootState G A b acc clock)
      (state G (UnitOrderRoots.residual G A b) (UnitOrderSemantics.savedOrder G A b++acc) clock) t ∧
      t≤100*(n+1)^2 := by
  let s := rootState G A b acc clock
  have h1 := clear_executes g (2 : Fin 46) s
  have h2 := moveOn_executes g (37 : Fin 46) 2 15 (by decide) (by decide) (by decide) (Function.update s 2 []) rfl
  let t := Function.update (Function.update (Function.update s 2 []) 2
    ((Function.update s 2 []) 37 ++ (Function.update s 2 []) 2)) 37 []
  have h3 := clear_executes g (38 : Fin 46) t
  have h4 := clear_executes g (8 : Fin 46) (Function.update t 38 [])
  have h5 := moveOn_executes g (43 : Fin 46) 45 15 (by decide) (by decide) (by decide)
    (Function.update (Function.update t 38 []) 8 []) rfl
  refine ⟨28*n+23+6*(UnitOrderRoots.savedBits G A b).length,?_,?_⟩
  · convert seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3
      (seq_executes _ _ g h4 h5))) using 1
    · funext i;fin_cases i <;> simp [s,t,state,rootState,UnitOrderRoots.state,
        UnitRecognitionComponent.store,UnitRecognitionChoice.rawState,labelBits_append,←savedBits_eq]
    · simp [s,t,state,rootState,UnitOrderRoots.state,
        UnitRecognitionComponent.store,UnitRecognitionChoice.rawState,liveBits_length];ring
  · have h := UnitOrderRoots.savedBits_length G A b
    nlinarith [Nat.zero_le (n^2)]

theorem body_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n) (A : Vector Bool n)
    (acc : List (Fin n)) (clock : BitString) :
    ∃t, body.Executes g (state G A acc clock)
      (state G (UnitOrderRoots.residual G A (UnitOrderRoots.find G A))
        (UnitOrderSemantics.savedOrder G A (UnitOrderRoots.find G A)++acc) clock) t ∧ t≤13000*(n+1)^6 := by
  obtain ⟨c,hc,hb⟩ := roots_executes g G A acc clock
  obtain ⟨d,hd,db⟩ := finish_executes g G A (UnitOrderRoots.find G A) acc clock
  refine ⟨_,seq_executes _ _ g (setup_executes g G A acc clock) (seq_executes _ _ g hc hd),?_⟩
  nlinarith [Nat.zero_le (n^2),Nat.zero_le (n^3),Nat.zero_le (n^4),Nat.zero_le (n^5),Nat.zero_le (n^6)]

noncomputable def loop : OracleBlock 45 := whilePop 44 body body
noncomputable def program : OracleBlock 45 := seq
  (copyOn 0 44 15 (by decide) (by decide) (by decide)) loop

lemma pop_clock {n : ℕ} (G : MatrixData n) (A : Vector Bool n) (acc : List (Fin n)) (clock : BitString) (b : Bool) :
    Function.update (state G A acc (b::clock)) (44 : Fin 46) clock=state G A acc clock := by
  funext i;fin_cases i <;> rfl

theorem loop_execution (g : BitString → ℕ) {n : ℕ} (G : MatrixData n) (m : ℕ)
    (A : Vector Bool n) (acc : List (Fin n)) :
    ∃t, WhileExecution (44 : Fin 46) body body g (state G A acc (List.replicate m true))
      (state G (run G m A acc).1 (run G m A acc).2 []) t ∧ t≤m*(13000*(n+1)^6+2)+1 := by
  induction m generalizing A acc with
  | zero => exact ⟨1,WhileExecution.empty _ rfl,by simp⟩
  | succ m ih =>
    obtain ⟨c,hc,hcb⟩ := body_executes g G A acc (List.replicate m true)
    obtain ⟨t,ht,htb⟩ := ih (UnitOrderRoots.residual G A (UnitOrderRoots.find G A))
      (UnitOrderSemantics.savedOrder G A (UnitOrderRoots.find G A)++acc)
    refine ⟨1+c+1+t,?_,?_⟩
    · exact WhileExecution.one (show state G A acc (List.replicate (m+1) true) 44=true::List.replicate m true from rfl)
        (by simpa only [List.replicate_succ,pop_clock] using hc) ht
    · nlinarith

theorem program_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (A : Vector Bool n) (acc : List (Fin n)) :
    ∃t, program.Executes g (state G A acc [])
      (state G (run G n A acc).1 (run G n A acc).2 []) t ∧ t≤16000*(n+1)^7 := by
  have h1 : (copyOn (0 : Fin 46) 44 15 (by decide) (by decide) (by decide)).Executes g
      (state G A acc []) (state G A acc (List.replicate n true)) (5*n+2) := by
    convert copyOn_executes g (0 : Fin 46) 44 15 (by decide) (by decide) (by decide) (state G A acc []) rfl using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state]
  obtain ⟨c,h2,b2⟩ := loop_execution g G n A acc
  refine ⟨_,seq_executes _ _ g h1 (whilePop_executes _ _ _ g h2),?_⟩
  nlinarith [Nat.zero_le (n^2),Nat.zero_le (n^3),Nat.zero_le (n^4),Nat.zero_le (n^5),Nat.zero_le (n^6),Nat.zero_le (n^7)]

/-- If every root trial fails, all original-n rounds literally preserve the
residual and accumulated array; a failed nonempty residual cannot vanish. -/
theorem program_stutters (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (A : Vector Bool n) (acc : List (Fin n)) (h : UnitOrderRoots.find G A=none) :
    ∃t, program.Executes g (state G A acc []) (state G A acc []) t ∧ t≤16000*(n+1)^7 := by
  obtain ⟨t,ht,hb⟩ := program_executes g G A acc
  have hs : run G n A acc=(A,acc) := UnitOrderSemantics.run_stuck G n A acc h
  rw [hs] at ht
  exact ⟨t,ht,hb⟩

lemma setup_queryFree : setup.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (push_queryFree _ _) (push_queryFree _ _))
lemma finish_queryFree : finish.QueryFree := seq_queryFree _ _ (clear_queryFree _)
  (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (clear_queryFree _)
    (seq_queryFree _ _ (clear_queryFree _) (moveOn_queryFree _ _ _ _ _ _))))
lemma body_queryFree : body.QueryFree := seq_queryFree _ _ setup_queryFree (seq_queryFree _ _
  (rename_queryFree _ _ UnitOrderRoots.program_queryFree) finish_queryFree)
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (whilePop_queryFree _ _ _ body_queryFree body_queryFree)

end HiddenCircuits.GraphReduction.Runtime.UnitOrderRounds
