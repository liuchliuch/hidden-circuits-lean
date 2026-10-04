import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionRootsLoop
import HiddenCircuits.Complexity.OracleMove

/-! Actual bounded residual-component rounds. A failed root search keeps its
alive mask unchanged, so failure cannot accidentally become acceptance. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRecognitionRounds
open Complexity Complexity.OracleBlock DH.Runtime.PairCheck

def round {n : ℕ} (G : MatrixData n) (A : Vector Bool n) : Vector Bool n :=
  UnitRecognitionRoots.residual G A (UnitRecognitionRoots.find G A)
def run {n : ℕ} (G : MatrixData n) : ℕ → Vector Bool n → Vector Bool n
  | 0,A => A
  | m+1,A => run G m (round G A)
def accepts {n : ℕ} (G : MatrixData n) : Bool :=
  (run G n (Vector.replicate n true)).toList.all Bool.not

def state {n : ℕ} (G : MatrixData n) (A : Vector Bool n) (clock : BitString) : Store 43 := fun r=>
  if r.val=0 then List.replicate n true else if r.val=1 then G.bits
  else if r.val=2 then liveBits A else if r.val=43 then clock else []
def rootState {n : ℕ} (G : MatrixData n) (A : Vector Bool n) (b : UnitRecognitionRoots.Best n)
    (clock : BitString) : Store 43 := fun r=>
  if h:r.val<43 then UnitRecognitionRoots.state G A b 0 none [] [] [] [] [] [] ⟨r.val,h⟩ else clock

def rootsEmbedding : Fin 43 ↪ Fin 44 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun z : Fin 44=>z.val) h)
noncomputable def setup : OracleBlock 43 := seq
  (copyOn 2 37 15 (by decide) (by decide) (by decide)) (seq (push 38 false) (push 8 false))
noncomputable def roots : OracleBlock 43 := rename UnitRecognitionRoots.program rootsEmbedding
noncomputable def finish : OracleBlock 43 := seq (clear 2)
  (seq (moveOn 37 2 15 (by decide) (by decide) (by decide)) (seq (clear 38) (clear 8)))
noncomputable def body : OracleBlock 43 := seq setup (seq roots finish)

theorem setup_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n) (A : Vector Bool n) (clock : BitString) :
    setup.Executes g (state G A clock) (rootState G A none clock) (20*n+8) := by
  have h1 := copyOn_executes g (2 : Fin 44) 37 15 (by decide) (by decide) (by decide) (state G A clock) rfl
  have h2 := push_executes g (38 : Fin 44) false (Function.update (state G A clock) 37 ((state G A clock) 2++(state G A clock) 37))
  have h3 := push_executes g (8 : Fin 44) false
    (Function.update (Function.update (state G A clock) 37 ((state G A clock) 2++(state G A clock) 37)) 38
      (false::(Function.update (state G A clock) 37 ((state G A clock) 2++(state G A clock) 37)) 38))
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 h3) using 1
  · funext i;fin_cases i <;> simp [state,rootState,UnitRecognitionRoots.state,UnitRecognitionRoots.residual,
      UnitRecognitionComponent.store,UnitRecognitionChoice.rawState]
  · simp [state,liveBits_length];ring

theorem roots_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n) (A : Vector Bool n) (clock : BitString) :
    ∃t, roots.Executes g (rootState G A none clock) (rootState G A (UnitRecognitionRoots.find G A) clock) t ∧
      t≤12000*(n+1)^6 := by
  obtain ⟨t,ht,hb⟩ := UnitRecognitionRoots.program_executes g G A
  refine ⟨t,?_,hb⟩
  apply rename_executes_to UnitRecognitionRoots.program rootsEmbedding g ht
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have h : ¬i.val<43 := by intro hh;exact hi ⟨i.val,hh⟩ (Fin.ext rfl)
    simp [rootState,h]

theorem finish_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n) (A : Vector Bool n)
    (b : UnitRecognitionRoots.Best n) (clock : BitString) :
    finish.Executes g (rootState G A b clock) (state G (UnitRecognitionRoots.residual G A b) clock) (28*n+16) := by
  let s := rootState G A b clock
  have h1 := clear_executes g (2 : Fin 44) s
  have h2 := moveOn_executes g (37 : Fin 44) 2 15 (by decide) (by decide) (by decide) (Function.update s 2 []) rfl
  let t := Function.update (Function.update (Function.update s 2 []) 2
    ((Function.update s 2 []) 37 ++ (Function.update s 2 []) 2)) 37 []
  have h3 := clear_executes g (38 : Fin 44) t
  have h4 := clear_executes g (8 : Fin 44) (Function.update t 38 [])
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)) using 1
  · funext i;fin_cases i <;> simp [s,t,state,rootState,UnitRecognitionRoots.state,
      UnitRecognitionComponent.store,UnitRecognitionChoice.rawState]
  · simp [s,t,state,rootState,UnitRecognitionRoots.state,
      UnitRecognitionComponent.store,UnitRecognitionChoice.rawState,liveBits_length];ring

theorem body_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n) (A : Vector Bool n) (clock : BitString) :
    ∃t, body.Executes g (state G A clock) (state G (round G A) clock) t ∧ t≤13000*(n+1)^6 := by
  obtain ⟨c,hc,hb⟩ := roots_executes g G A clock
  refine ⟨_,seq_executes _ _ g (setup_executes g G A clock)
    (seq_executes _ _ g hc (finish_executes g G A (UnitRecognitionRoots.find G A) clock)),?_⟩
  nlinarith [Nat.zero_le (n^2),Nat.zero_le (n^3),Nat.zero_le (n^4),Nat.zero_le (n^5),Nat.zero_le (n^6)]

noncomputable def loop : OracleBlock 43 := whilePop 43 body body
noncomputable def program : OracleBlock 43 := seq
  (copyOn 0 43 15 (by decide) (by decide) (by decide)) loop

lemma pop_clock {n : ℕ} (G : MatrixData n) (A : Vector Bool n) (clock : BitString) (b : Bool) :
    Function.update (state G A (b::clock)) (43 : Fin 44) clock=state G A clock := by
  funext i;fin_cases i <;> rfl

theorem loop_execution (g : BitString → ℕ) {n : ℕ} (G : MatrixData n) (m : ℕ) (A : Vector Bool n) :
    ∃t, WhileExecution (43 : Fin 44) body body g (state G A (List.replicate m true))
      (state G (run G m A) []) t ∧ t≤m*(13000*(n+1)^6+2)+1 := by
  induction m generalizing A with
  | zero => exact ⟨1,WhileExecution.empty _ rfl,by simp⟩
  | succ m ih =>
    obtain ⟨c,hc,hcb⟩ := body_executes g G A (List.replicate m true)
    obtain ⟨t,ht,htb⟩ := ih (round G A)
    refine ⟨1+c+1+t,?_,?_⟩
    · exact WhileExecution.one (show state G A (List.replicate (m+1) true) 43=true::List.replicate m true from rfl)
        (by simpa only [List.replicate_succ,pop_clock] using hc) ht
    · nlinarith

theorem program_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n) (A : Vector Bool n) :
    ∃t, program.Executes g (state G A []) (state G (run G n A) []) t ∧ t≤14000*(n+1)^7 := by
  have h1 : (copyOn (0 : Fin 44) 43 15 (by decide) (by decide) (by decide)).Executes g
      (state G A []) (state G A (List.replicate n true)) (5*n+2) := by
    convert copyOn_executes g (0 : Fin 44) 43 15 (by decide) (by decide) (by decide) (state G A []) rfl using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state]
  obtain ⟨c,h2,b2⟩ := loop_execution g G n A
  refine ⟨_,seq_executes _ _ g h1 (whilePop_executes _ _ _ g h2),?_⟩
  nlinarith [Nat.zero_le (n^2),Nat.zero_le (n^3),Nat.zero_le (n^4),Nat.zero_le (n^5),Nat.zero_le (n^6),Nat.zero_le (n^7)]

lemma setup_queryFree : setup.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (push_queryFree _ _) (push_queryFree _ _))
lemma finish_queryFree : finish.QueryFree := seq_queryFree _ _ (clear_queryFree _)
  (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _)))
lemma body_queryFree : body.QueryFree := seq_queryFree _ _ setup_queryFree (seq_queryFree _ _
  (rename_queryFree _ _ UnitRecognitionRoots.program_queryFree) finish_queryFree)
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (whilePop_queryFree _ _ _ body_queryFree body_queryFree)

end HiddenCircuits.GraphReduction.Runtime.UnitRecognitionRounds
