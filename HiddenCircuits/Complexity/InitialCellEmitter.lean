import HiddenCircuits.Complexity.CNFEmitter
import HiddenCircuits.Complexity.OracleStream
import HiddenCircuits.Complexity.InitialNetworkCNF
import HiddenCircuits.Complexity.PolynomialBounds

/-! Actual finite emission of initial tableau cells. Unary source and dense target
indices are preserved, scratch stacks are cleared, and the output is the exact
reversed canonical CNF stream, in the original truth-table enumeration order. -/
namespace HiddenCircuits.Complexity.InitialCellEmitter
open OracleBlock Polynomial

/-- Read-only source0 and target1, index work2, copy work3, reversed output4. -/
def state (source target counter temporary : ℕ) (stream : BitString) : Store 4 := fun i =>
  if i.val=4 then stream else List.replicate (if i.val=0 then source else if i.val=1 then target
    else if i.val=2 then counter else temporary) true

lemma update_stream (source target counter temporary : ℕ) (old stream : BitString) :
    Function.update (state source target counter temporary old) 4 stream =
      state source target counter temporary stream := by
  funext i; fin_cases i <;> rfl

def port (target : Bool) : Fin 5 := if target then 1 else 0

def index (source target : ℕ) (which : Bool) : ℕ := if which then target else source

noncomputable def literal (which sign : Bool) : OracleBlock 4 :=
  seq (copyOn (port which) 2 3 (by cases which <;> decide)
    (by cases which <;> decide) (by decide)) (CNFEmitter.literal 2 4 sign)

/-- Actual read-only literal emission; copying and each serializer instruction
are included in the exact charge. -/
theorem literal_executes (g : BitString → ℕ) (which sign : Bool)
    (source target : ℕ) (stream : BitString) :
    (literal which sign).Executes g (state source target 0 0 stream)
      (state source target 0 0 ((serializedLiteral (index source target which) sign).reverse++stream))
      (32*index source target which+47) := by
  have hc : (copyOn (port which) (2 : Fin 5) 3 (by cases which <;> decide)
      (by cases which <;> decide) (by decide)).Executes g
      (state source target 0 0 stream) (state source target (index source target which) 0 stream)
      (5*index source target which+2) := by
    have h := copyOn_executes g (port which) (2 : Fin 5) 3 (by cases which <;> decide)
      (by cases which <;> decide) (by decide) (state source target 0 0 stream) rfl
    convert h using 1
    · funext i; cases which <;> fin_cases i <;> simp [state,port,index]
    · cases which <;> simp [state,port,index]
  have hl : (CNFEmitter.literal (2 : Fin 5) 4 sign).Executes g
      (state source target (index source target which) 0 stream)
      (state source target 0 0 ((serializedLiteral (index source target which) sign).reverse++stream))
      (27*index source target which+43) := by
    have h := CNFEmitter.literal_executes g (2 : Fin 5) 4 (by decide) sign
      (state source target (index source target which) 0 stream)
    convert h using 1
    · funext i; fin_cases i <;> simp [state]
    · simp [state]
  convert seq_executes _ _ g hc hl using 1 <;> omega

lemma literal_queryFree (which sign : Bool) : (literal which sign).QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (CNFEmitter.literal_queryFree _ _ _)

inductive Item
  | start
  | literal (which sign : Bool)
  | finish

noncomputable def itemBlock : Item → OracleBlock 4
  | .start => push 4 true
  | .literal which sign => literal which sign
  | .finish => push 4 false

def itemChunk (source target : ℕ) : Item → BitString
  | .start => [true]
  | .literal which sign => serializedLiteral (index source target which) sign
  | .finish => [false]

def itemCost (source target : ℕ) : Item → ℕ
  | .start => 1
  | .literal which _ => 32*index source target which+47
  | .finish => 1

theorem items_executes (g : BitString → ℕ) (items : List Item)
    (source target : ℕ) (stream : BitString) :
    (sequence (items.map itemBlock)).Executes g (state source target 0 0 stream)
      (state source target 0 0 ((items.flatMap (itemChunk source target)).reverse++stream))
      ((items.map (itemCost source target)).sum+2*items.length+1) := by
  have hitem (a : Item) (_ : a ∈ items) (acc : BitString) :
      (itemBlock a).Executes g (Function.update (state source target 0 0 []) 4 acc)
        (Function.update (state source target 0 0 []) 4 ((itemChunk source target a).reverse++acc))
        (itemCost source target a) := by
    simp only [update_stream]
    cases a with
    | start => simpa only [update_stream] using push_executes g (4 : Fin 5) true (state source target 0 0 acc)
    | finish => simpa only [update_stream] using push_executes g (4 : Fin 5) false (state source target 0 0 acc)
    | literal which sign => exact literal_executes g which sign source target acc
  simpa only [update_stream] using sequence_emit g items itemBlock (itemChunk source target)
    (itemCost source target) (state source target 0 0 []) 4 hitem stream

lemma items_queryFree (items : List Item) : (sequence (items.map itemBlock)).QueryFree := by
  apply sequence_queryFree
  intro B hb
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp hb
  cases a with
  | start => exact push_queryFree _ _
  | finish => exact push_queryFree _ _
  | literal which sign => exact literal_queryFree _ _

def constantItems (value : Bool) : List Item := [.start,.literal true value,.finish]
noncomputable def constant (value : Bool) : OracleBlock 4 := sequence ((constantItems value).map itemBlock)

theorem constant_executes (g : BitString → ℕ) (value : Bool)
    (source target : ℕ) (stream : BitString) :
    (constant value).Executes g (state source target 0 0 stream)
      (state source target 0 0 ((serializedClause [(target,value)]).reverse++stream)) (32*target+56) := by
  convert items_executes g (constantItems value) source target stream using 1
  · simp [constantItems,itemChunk,index,serializedClause]
  · simp [constantItems,itemCost,index]; omega

lemma constant_queryFree (value : Bool) : (constant value).QueryFree := items_queryFree _

def bitItems (negate value : Bool) : List Item :=
  [.start,.literal false (!value),.literal true (Bool.xor value negate),.finish]
noncomputable def bitClause (negate value : Bool) : OracleBlock 4 := sequence ((bitItems negate value).map itemBlock)

def rawBitClause (source target : ℕ) (negate value : Bool) : List (ℕ × Bool) :=
  [(source,!value),(target,Bool.xor value negate)]

theorem bitClause_executes (g : BitString → ℕ) (negate value : Bool)
    (source target : ℕ) (stream : BitString) :
    (bitClause negate value).Executes g (state source target 0 0 stream)
      (state source target 0 0 ((serializedClause (rawBitClause source target negate value)).reverse++stream))
      (32*(source+target)+105) := by
  have h := items_executes g (bitItems negate value) source target stream
  convert h using 1
  · simp [bitItems,itemChunk,index,serializedClause,rawBitClause,List.append_assoc]
  · simp [bitItems,itemCost,index]; omega

lemma bitClause_queryFree (negate value : Bool) : (bitClause negate value).QueryFree := items_queryFree _

noncomputable def patterns : List (Fin 1 → Bool) := Finset.univ.toList
lemma patterns_length : patterns.length = 2 := by
  classical
  simp [patterns]

noncomputable def bitBits (source target : ℕ) (negate : Bool) : BitString :=
  patterns.flatMap (fun a => serializedClause (rawBitClause source target negate (a 0)))

noncomputable def bit (negate : Bool) : OracleBlock 4 :=
  sequence (patterns.map (fun a => bitClause negate (a 0)))

/-- Both equivalence clauses are emitted in the very same finite enumeration
order as TruthTableCNF.clauses, with all metadata restored. -/
theorem bit_executes (g : BitString → ℕ) (negate : Bool)
    (source target : ℕ) (stream : BitString) :
    (bit negate).Executes g (state source target 0 0 stream)
      (state source target 0 0 ((bitBits source target negate).reverse++stream))
      (64*(source+target)+215) := by
  have hitem (a : Fin 1 → Bool) (_ : a ∈ patterns) (acc : BitString) :
      (bitClause negate (a 0)).Executes g (Function.update (state source target 0 0 []) 4 acc)
        (Function.update (state source target 0 0 []) 4
          ((serializedClause (rawBitClause source target negate (a 0))).reverse++acc))
        (32*(source+target)+105) := by
    simpa only [update_stream] using bitClause_executes g negate (a 0) source target acc
  have h := sequence_emit g patterns (fun a => bitClause negate (a 0))
    (fun a => serializedClause (rawBitClause source target negate (a 0))) (fun _ => 32*(source+target)+105)
    (state source target 0 0 []) 4 hitem stream
  convert h using 1
  · rw [update_stream]
  · rw [update_stream]; rfl
  · simp [List.map_const,patterns_length]; omega

lemma bit_queryFree (negate : Bool) : (bit negate).QueryFree := by
  apply sequence_queryFree
  intro B hb
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp hb
  exact bitClause_queryFree _ _

end HiddenCircuits.Complexity.InitialCellEmitter
