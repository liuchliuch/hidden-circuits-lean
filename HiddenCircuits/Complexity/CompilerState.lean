import HiddenCircuits.Complexity.VerifierSetup
import HiddenCircuits.Complexity.InitialRowRuntime
import HiddenCircuits.Complexity.TimeCorrectness

/-! Shared eighteen-stack layout for the complete verifier-to-CNF compiler. -/
namespace HiddenCircuits.Complexity.CompilerState
open OracleBlock TM2BooleanEncoding

structure Registers where
  source : ℕ := 0
  base : ℕ := 0
  nextBase : ℕ := 0
  remaining : ℕ := 0
  clock : ℕ := 0
  height : ℕ := 0
  cells : ℕ := 0
  witnesses : ℕ := 0
  varCount : ℕ := 0
  target : ℕ := 0
  inputCopy : BitString := []
  witnessClock : ℕ := 0
  stream : BitString := []

def store (x : BitString) (R : Registers) : Store 17 := fun i =>
  if i.val=6 then R.stream else if i.val=11 then x else if i.val=16 then R.inputCopy else
    List.replicate (if i.val=0 then R.source else if i.val=1 then R.base else if i.val=5 then R.remaining
      else if i.val=7 then R.nextBase else if i.val=8 then R.clock else if i.val=9 then R.height
      else if i.val=10 then R.cells else if i.val=12 then x.length else if i.val=13 then R.witnesses
      else if i.val=14 then R.varCount else if i.val=15 then R.target else if i.val=17 then R.witnessClock else 0) true

lemma update_stream (x : BitString) (R : Registers) (s : BitString) :
    Function.update (store x R) 6 s = store x {R with stream := s} := by
  funext i;fin_cases i <;> rfl

def headerBits (n : ℕ) : BitString := List.replicate (2*n) true++[false]

noncomputable def header : OracleBlock 17 := CNFEmitter.header 14 6

theorem header_executes (g : BitString → ℕ) (x : BitString) (R : Registers) :
    header.Executes g (store x R)
      (store x {R with varCount:=0,stream:=(headerBits R.varCount).reverse++R.stream}) (9*R.varCount+4) := by
  have h := CNFEmitter.header_executes g (14 : Fin 18) 6 (by decide) (store x R)
  convert h using 1
  · funext i;fin_cases i <;> simp [store,headerBits]
  · simp [store]

def initialEmbedding : Fin 12 ↪ Fin 18 where
  toFun i := if i.val=0 then 0 else if i.val=1 then 15 else if i.val=2 then 2 else if i.val=3 then 3
    else if i.val=4 then 6 else if i.val=5 then 11 else if i.val=6 then 13 else if i.val=7 then 9
    else if i.val=8 then 16 else if i.val=9 then 5 else if i.val=10 then 17 else 4
  inj' := by decide

variable {v : BitString → Bool}
variable (M : Turing.TM2ComputableInPolyTime id Computability.encodeBool v)

noncomputable def initial : OracleBlock 17 := rename (InitialRowEmitter.program M) initialEmbedding

theorem initial_executes (g : BitString → ℕ) (x : BitString) (R : Registers)
    (hs : R.source=0) (ht : R.target=0) (hi : R.inputCopy=[]) (hr : R.remaining=0) (hw : R.witnessClock=0)
    (hH : 2*x.length+R.witnesses+1≤R.height) :
    ∃ cost, (initial M).Executes g (store x R)
      (store x {R with source:=R.witnesses,target:=R.witnesses+bitCount M.tm R.height, stream:=(InitialRowEmitter.bits M x R.witnesses R.height).reverse++R.stream}) cost ∧
      cost ≤ 5*x.length+10*R.witnesses+5*R.height+34+
        InitialRowEmitter.familyBound R.witnesses (R.witnesses+bitCount M.tm R.height) (controlBits M.tm)+
        R.height*(InitialRowEmitter.familyBound R.witnesses (R.witnesses+bitCount M.tm R.height) (symbolBits M.tm)+8) := by
  obtain ⟨cost,hc,hb⟩ := InitialRowEmitter.program_executes M g x R.witnesses R.height hH R.stream
  refine ⟨cost,?_,hb⟩
  apply rename_executes_to _ initialEmbedding g hc
  · funext i;fin_cases i <;> simp [store,initialEmbedding,InitialRowEmitter.state,hs,ht,hi,hr,hw]
  · funext i;fin_cases i <;> simp [store,initialEmbedding,InitialRowEmitter.state,hs,ht,hi,hr,hw]
  · intro i hi
    fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | exact (hi 4 rfl).elim

noncomputable def clearInitial : OracleBlock 17 := seq (clear 0) (clear 15)

theorem clearInitial_executes (g : BitString → ℕ) (x : BitString) (R : Registers) :
    clearInitial.Executes g (store x R) (store x {R with source:=0,target:=0}) (R.source+R.target+4) := by
  have h₁ : (clear (0 : Fin 18)).Executes g (store x R) (store x {R with source:=0}) (R.source+1) := by
    convert clear_executes g (0 : Fin 18) (store x R) using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  have h₂ : (clear (15 : Fin 18)).Executes g (store x {R with source:=0})
      (store x {R with source:=0,target:=0}) (R.target+1) := by
    convert clear_executes g (15 : Fin 18) (store x {R with source:=0}) using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  convert seq_executes _ _ g h₁ h₂ using 1 <;> omega

noncomputable def bases : OracleBlock 17 := seq
  (copyOn 13 1 4 (by decide) (by decide) (by decide))
  (seq (copyOn 13 7 4 (by decide) (by decide) (by decide)) (copyOn 10 7 4 (by decide) (by decide) (by decide)))

theorem bases_executes (g : BitString → ℕ) (x : BitString) (R : Registers) :
    bases.Executes g (store x R) (store x {R with base:=R.witnesses+R.base,nextBase:=R.cells+R.witnesses+R.nextBase})
      (10*R.witnesses+5*R.cells+10) := by
  have h₁ : (copyOn (13 : Fin 18) 1 4 (by decide) (by decide) (by decide)).Executes g
      (store x R) (store x {R with base:=R.witnesses+R.base}) (5*R.witnesses+2) := by
    convert copyOn_executes g (13 : Fin 18) 1 4 (by decide) (by decide) (by decide) (store x R) rfl using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  have h₂ : (copyOn (13 : Fin 18) 7 4 (by decide) (by decide) (by decide)).Executes g
      (store x {R with base:=R.witnesses+R.base})
      (store x {R with base:=R.witnesses+R.base,nextBase:=R.witnesses+R.nextBase}) (5*R.witnesses+2) := by
    convert copyOn_executes g (13 : Fin 18) 7 4 (by decide) (by decide) (by decide)
      (store x {R with base:=R.witnesses+R.base}) rfl using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  have h₃ : (copyOn (10 : Fin 18) 7 4 (by decide) (by decide) (by decide)).Executes g
      (store x {R with base:=R.witnesses+R.base,nextBase:=R.witnesses+R.nextBase})
      (store x {R with base:=R.witnesses+R.base,nextBase:=R.cells+R.witnesses+R.nextBase}) (5*R.cells+2) := by
    convert copyOn_executes g (10 : Fin 18) 7 4 (by decide) (by decide) (by decide)
      (store x {R with base:=R.witnesses+R.base,nextBase:=R.witnesses+R.nextBase}) rfl using 1
    · funext i;fin_cases i <;> simp [store,Nat.add_assoc]
    · simp [store]
  convert seq_executes _ _ g h₁ (seq_executes _ _ g h₂ h₃) using 1 <;> omega

def transitionEmbedding : Fin 11 ↪ Fin 18 where
  toFun i := ⟨i.val,by have := i.isLt;omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun q : Fin 18 => q.val) h)

noncomputable def transitions : OracleBlock 17 := rename (TimeEmitter.program M.tm) transitionEmbedding

theorem transitions_executes (g : BitString → ℕ) (x : BitString) (R : Registers)
    (hs : R.source=0) (hr : R.remaining=0) (hH : 0<R.height) :
    ∃ cost, (transitions M).Executes g (store x R)
      (store x {R with base:=R.base+R.clock*R.cells,nextBase:=R.nextBase+R.clock*R.cells,clock:=0, stream:=(TimeEmitter.bits M.tm R.height R.cells R.base R.nextBase R.clock).reverse++R.stream}) cost ∧
      cost ≤ (TimeEmitter.time M.tm).eval (R.height+R.base+R.nextBase+R.clock+R.cells) := by
  obtain ⟨cost,hc,hb⟩ := TimeEmitter.program_executes g M.tm R.base R.nextBase R.clock R.height R.cells hH R.stream
  refine ⟨cost,?_,hb⟩
  apply rename_executes_to _ transitionEmbedding g hc
  · funext i;fin_cases i <;> simp [store,TimeEmitter.state,hs,hr,transitionEmbedding]
  · funext i;fin_cases i <;> simp [store,TimeEmitter.state,hs,hr,transitionEmbedding]
  · intro i hi
    fin_cases i <;> first | rfl | exact (hi 1 rfl).elim | exact (hi 6 rfl).elim | exact (hi 7 rfl).elim | exact (hi 8 rfl).elim

noncomputable def initialClean : OracleBlock 17 := InitialRowEmitter.cleanProgramOn M initialEmbedding

theorem initialClean_executes (g : BitString → ℕ) (x : BitString) (R : Registers)
    (hs : R.source=0) (ht : R.target=0) (hi : R.inputCopy=[]) (hr : R.remaining=0) (hw : R.witnessClock=0)
    (hH : 2*x.length+R.witnesses+1≤R.height) :
    ∃ cost, (initialClean M).Executes g (store x R)
      (store x {R with stream:=(InitialRowEmitter.bits M x R.witnesses R.height).reverse++R.stream}) cost ∧
      cost ≤ (InitialRowEmitter.cleanTime M).eval (x.length+R.witnesses+R.height) := by
  have hp : (store x R) ∘ initialEmbedding = InitialRowEmitter.state 0 0 x R.witnesses R.height [] 0 0
      ((store x R) (initialEmbedding 4)) := by
    funext i;fin_cases i <;> simp [store,initialEmbedding,InitialRowEmitter.state,hs,ht,hi,hr,hw]
  obtain ⟨cost,hc,hb⟩ := InitialRowEmitter.cleanProgramOn_executes M initialEmbedding g (store x R) x
    R.witnesses R.height hH hp
  refine ⟨cost,?_,hb⟩
  have he : initialEmbedding 4 = 6 := rfl
  rw [he] at hc
  simpa only [update_stream] using hc

lemma initialClean_queryFree : (initialClean M).QueryFree := InitialRowEmitter.cleanProgramOn_queryFree M _

lemma header_queryFree : header.QueryFree := CNFEmitter.header_queryFree _ _
lemma initial_queryFree : (initial M).QueryFree := rename_queryFree _ _ (InitialRowEmitter.program_queryFree M)
lemma clearInitial_queryFree : clearInitial.QueryFree := seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _)
lemma bases_queryFree : bases.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (copyOn_queryFree _ _ _ _ _ _))
lemma transitions_queryFree : (transitions M).QueryFree := rename_queryFree _ _ (TimeEmitter.program_queryFree M.tm)

end HiddenCircuits.Complexity.CompilerState
