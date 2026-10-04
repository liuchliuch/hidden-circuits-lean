import HiddenCircuits.Complexity.OutputLiteralEmitter
import HiddenCircuits.Complexity.OracleStream

/-! Complete finite-machine emission of a local truth-table clause. The previous
and next row bases are separate preserved registers; all index work registers
return empty, and the emitted stream is exactly the canonical CNF clause chunk. -/
namespace HiddenCircuits.Complexity.LocalClauseEmitter
open OracleBlock TM2BooleanEncoding OutputLiteralEmitter Polynomial

/-- Registers0..6 match PortLiteralEmitter; register7 holds the next-row base. -/
def state (j base nextBase index counter temporary r : ℕ) (stream : BitString) : Store 7 := fun i =>
  if i.val=6 then stream else List.replicate (if i.val=0 then j else if i.val=1 then base
    else if i.val=2 then index else if i.val=3 then counter else if i.val=4 then temporary
    else if i.val=5 then r else nextBase) true

def nextRowEmbedding : Fin 7 ↪ Fin 8 where
  toFun i := ⟨if i.val=1 then 7 else i.val,by split_ifs <;> have := i.isLt <;> omega⟩
  inj' := by
    intro i j h
    have hv := congrArg Fin.val h
    dsimp at hv
    by_cases hi : i.val=1 <;> by_cases hj : j.val=1 <;> simp [hi,hj] at hv <;>
      apply Fin.ext <;> have := i.isLt <;> have := j.isLt <;> omega

noncomputable def portBlock (M : Turing.FinTM2) (p : Port M) (sign : Bool) : OracleBlock 7 :=
  rename (PortLiteralEmitter.program M p sign) (Fin.castAddEmb 1)
noncomputable def outputBlock (M : Turing.FinTM2) (f : Family M) (pattern : Port M → Bool) : OracleBlock 7 :=
  rename (OutputLiteralEmitter.program M f pattern) nextRowEmbedding

theorem portBlock_executes (g : BitString → ℕ) (M : Turing.FinTM2) (p : Port M) (sign : Bool)
    (j r base nextBase : ℕ) (stream : BitString) :
    ∃ cost, (portBlock M p sign).Executes g (state j base nextBase 0 0 0 r stream)
      (state j base nextBase 0 0 0 r
        ((serializedLiteral (base+portAddress M (j+r+1) j p) sign).reverse++stream)) cost ∧
      cost ≤ (PortLiteralEmitter.time M p).eval (j+r+base) := by
  obtain ⟨cost,hc,hb⟩ := PortLiteralEmitter.program_executes g M p sign j r base stream
  refine ⟨cost,?_,hb⟩
  apply rename_executes_to _ (Fin.castAddEmb 1) g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    fin_cases i
    · exact (hi 0 rfl).elim
    · exact (hi 1 rfl).elim
    · exact (hi 2 rfl).elim
    · exact (hi 3 rfl).elim
    · exact (hi 4 rfl).elim
    · exact (hi 5 rfl).elim
    · exact (hi 6 rfl).elim
    · rfl

theorem outputBlock_executes (g : BitString → ℕ) (M : Turing.FinTM2) (f : Family M) (pattern : Port M → Bool)
    (j r base nextBase : ℕ) (stream : BitString) :
    ∃ cost, (outputBlock M f pattern).Executes g (state j base nextBase 0 0 0 r stream)
      (state j base nextBase 0 0 0 r
        ((serializedLiteral (nextBase+(cellEnumeration M (j+r+1) (familyCell M j r f)).val)
          (directRule M (j+r+1) (familyCell M j r f) pattern)).reverse++stream)) cost ∧
      cost ≤ (OutputLiteralEmitter.time M f).eval (j+r+nextBase) := by
  obtain ⟨cost,hc,hb⟩ := OutputLiteralEmitter.program_executes g M f pattern j r nextBase stream
  refine ⟨cost,?_,hb⟩
  apply rename_executes_to _ nextRowEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    fin_cases i
    · exact (hi 0 rfl).elim
    · rfl
    · exact (hi 2 rfl).elim
    · exact (hi 3 rfl).elim
    · exact (hi 4 rfl).elim
    · exact (hi 5 rfl).elim
    · exact (hi 6 rfl).elim
    · exact (hi 1 rfl).elim

inductive Item (M : Turing.FinTM2)
  | start
  | port (p : Port M)
  | output
  | finish

noncomputable def ports (M : Turing.FinTM2) : List (Port M) :=
  List.ofFn (fun i => (portEnumeration M).symm i)
noncomputable def items (M : Turing.FinTM2) : List (Item M) :=
  Item.start :: (ports M).map Item.port ++ [Item.output,Item.finish]

noncomputable def itemBlock (M : Turing.FinTM2) (f : Family M) (pattern : Port M → Bool) : Item M → OracleBlock 7
  | .start => push 6 true
  | .port p => portBlock M p (!(pattern p))
  | .output => outputBlock M f pattern
  | .finish => push 6 false

noncomputable def rawClause (M : Turing.FinTM2) (f : Family M) (pattern : Port M → Bool)
    (j r base nextBase : ℕ) : List (ℕ × Bool) :=
  (ports M).map (fun p => (base+portAddress M (j+r+1) j p,!(pattern p))) ++
    [(nextBase+(cellEnumeration M (j+r+1) (familyCell M j r f)).val,
      directRule M (j+r+1) (familyCell M j r f) pattern)]

noncomputable def itemChunk (M : Turing.FinTM2) (f : Family M) (pattern : Port M → Bool)
    (j r base nextBase : ℕ) : Item M → BitString
  | .start => [true]
  | .port p => serializedLiteral (base+portAddress M (j+r+1) j p) (!(pattern p))
  | .output => serializedLiteral (nextBase+(cellEnumeration M (j+r+1) (familyCell M j r f)).val)
      (directRule M (j+r+1) (familyCell M j r f) pattern)
  | .finish => [false]

lemma chunks_eq_clause (M : Turing.FinTM2) (f : Family M) (pattern : Port M → Bool) (j r base nextBase : ℕ) :
    (items M).flatMap (itemChunk M f pattern j r base nextBase) = serializedClause (rawClause M f pattern j r base nextBase) := by
  simp [items,itemChunk,serializedClause,rawClause,List.flatMap_map,List.append_assoc]

noncomputable def itemTime (M : Turing.FinTM2) (f : Family M) : Item M → Polynomial ℕ
  | .start => 1
  | .port p => PortLiteralEmitter.time M p
  | .output => OutputLiteralEmitter.time M f
  | .finish => 1

noncomputable def sumTimes (M : Turing.FinTM2) (f : Family M) : List (Item M) → Polynomial ℕ
  | [] => 0
  | a::as => itemTime M f a+sumTimes M f as

lemma sumTimes_eval (M : Turing.FinTM2) (f : Family M) (is : List (Item M)) (n : ℕ) :
    (sumTimes M f is).eval n = (is.map (fun a => (itemTime M f a).eval n)).sum := by
  induction is <;> simp [sumTimes, *]

noncomputable def program (M : Turing.FinTM2) (f : Family M) (pattern : Port M → Bool) : OracleBlock 7 :=
  sequence ((items M).map (itemBlock M f pattern))
noncomputable def time (M : Turing.FinTM2) (f : Family M) : Polynomial ℕ :=
  sumTimes M f (items M)+C (2*(items M).length+1)

lemma update_stream (j base nextBase index counter temporary r : ℕ) (old stream : BitString) :
    Function.update (state j base nextBase index counter temporary r old) 6 stream =
      state j base nextBase index counter temporary r stream := by
  funext i;fin_cases i <;> rfl

/-- The entire local clause, including boundaries, every input literal and the
computed output literal, is emitted by one actual finite program. -/
theorem program_executes (g : BitString → ℕ) (M : Turing.FinTM2) (f : Family M) (pattern : Port M → Bool)
    (j r base nextBase : ℕ) (stream : BitString) :
    ∃ cost, (program M f pattern).Executes g (state j base nextBase 0 0 0 r stream)
      (state j base nextBase 0 0 0 r
        ((serializedClause (rawClause M f pattern j r base nextBase)).reverse++stream)) cost ∧
      cost ≤ (time M f).eval (j+r+base+nextBase) := by
  let n := j+r+base+nextBase
  have hitem (a : Item M) (_ : a ∈ items M) (acc : BitString) : ∃ cost,
      (itemBlock M f pattern a).Executes g
        (Function.update (state j base nextBase 0 0 0 r []) 6 acc)
        (Function.update (state j base nextBase 0 0 0 r []) 6 ((itemChunk M f pattern j r base nextBase a).reverse++acc)) cost ∧
      cost ≤ (itemTime M f a).eval n := by
    simp only [update_stream]
    cases a with
    | start =>
      refine ⟨1,?_,by simp [itemTime]⟩
      simpa only [update_stream] using push_executes g (6 : Fin 8) true (state j base nextBase 0 0 0 r acc)
    | finish =>
      refine ⟨1,?_,by simp [itemTime]⟩
      simpa only [update_stream] using push_executes g (6 : Fin 8) false (state j base nextBase 0 0 0 r acc)
    | port p =>
      obtain ⟨cost,hc,hb⟩ := portBlock_executes g M p (!(pattern p)) j r base nextBase acc
      exact ⟨cost,hc,hb.trans (polynomial_nat_eval_mono _ (by dsimp [n];omega))⟩
    | output =>
      obtain ⟨cost,hc,hb⟩ := outputBlock_executes g M f pattern j r base nextBase acc
      exact ⟨cost,hc,hb.trans (polynomial_nat_eval_mono _ (by dsimp [n];omega))⟩
  obtain ⟨cost,hc,hb⟩ := sequence_emit_bounded g (items M) (itemBlock M f pattern)
    (itemChunk M f pattern j r base nextBase) (fun a => (itemTime M f a).eval n)
    (state j base nextBase 0 0 0 r []) 6 hitem stream
  refine ⟨cost,?_,?_⟩
  · simpa only [chunks_eq_clause,update_stream] using hc
  · simpa only [time,Polynomial.eval_add,Polynomial.eval_C,sumTimes_eval] using hb

lemma program_queryFree (M : Turing.FinTM2) (f : Family M) (pattern : Port M → Bool) :
    (program M f pattern).QueryFree := by
  apply sequence_queryFree
  intro B hb
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp hb
  cases a with
  | start => exact push_queryFree _ _
  | finish => exact push_queryFree _ _
  | port p => exact rename_queryFree _ _ (PortLiteralEmitter.program_queryFree _ _ _)
  | output => exact rename_queryFree _ _ (OutputLiteralEmitter.program_queryFree _ _ _)

end HiddenCircuits.Complexity.LocalClauseEmitter
