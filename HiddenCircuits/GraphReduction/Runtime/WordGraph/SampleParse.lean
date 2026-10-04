import HiddenCircuits.GraphReduction.Runtime.WordGraph.WordParserCorrectness
import HiddenCircuits.GraphReduction.Runtime.WordGraph.SampleProgram

namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.WordSample
open Complexity OracleBlock BinaryArithmetic
set_option maxHeartbeats 800000

def state (w : WordInstance) (t : ℕ) (stream kind index out : BitString) (height : ℕ) (result : BitString := []) : Store 17 := fun i =>
  if i.val=7 then stream else if i.val=8 then kind else if i.val=9 then index
  else if i.val=12 then result else if i.val=14 then out else if i.val=16 then List.replicate height true
  else WordParser.state w t i

def atomEmbedding : Fin 8 ↪ Fin 18 where
  toFun i := (![8,9,6,14,16,10,11,13] : Fin 8 → Fin 18) i
  inj' := by decide +kernel
def outerEmbedding : Fin 4 ↪ Fin 18 where
  toFun i := (![7,9,10,13] : Fin 4 → Fin 18) i
  inj' := by decide +kernel
def innerEmbedding : Fin 4 ↪ Fin 18 where
  toFun i := (![9,8,10,13] : Fin 4 → Fin 18) i
  inj' := by decide +kernel
noncomputable def parseLetter : OracleBlock 17 := seq (Circuit.Runtime.SamplePairParser.on outerEmbedding)
  (Circuit.Runtime.SamplePairParser.on innerEmbedding)
noncomputable def emitLetter : OracleBlock 17 := rename SampleAtom.program atomEmbedding
noncomputable def body : OracleBlock 17 := seq parseLetter emitLetter

lemma parseLetter_executes (g : BitString → ℕ) (w : WordInstance) (l : Letter (2*w.particles)) (t : ℕ)
    (rest out : BitString) (height : ℕ) :
    parseLetter.Executes g (state w t (pairBits (letterBits l) rest) [] [] out height)
      (state w t rest (kindBits l.kind) (List.replicate l.index.val true) out height) (5*l.index.val+51) := by
  have ho : (Circuit.Runtime.SamplePairParser.on outerEmbedding).Executes g
      (state w t (pairBits (letterBits l) rest) [] [] out height)
      (state w t rest [] (letterBits l) out height) (5*(letterBits l).length+7) := by
    apply Circuit.Runtime.SamplePairParser.on_executes outerEmbedding g (letterBits l) rest
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim
  have hi : (Circuit.Runtime.SamplePairParser.on innerEmbedding).Executes g
      (state w t rest [] (letterBits l) out height)
      (state w t rest (kindBits l.kind) (List.replicate l.index.val true) out height) 17 := by
    convert Circuit.Runtime.SamplePairParser.on_executes innerEmbedding g (kindBits l.kind) (List.replicate l.index.val true)
      (state w t rest [] (letterBits l) out height)
      (state w t rest (kindBits l.kind) (List.replicate l.index.val true) out height)
      (by funext i;fin_cases i <;> rfl)
      (by funext i;fin_cases i <;> rfl)
      (by intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim) using 1
    simp only [kindBits_length]
  convert seq_executes _ _ g ho hi using 1
  rw [letterBits_length]
  omega

lemma emitLetter_executes (g : BitString → ℕ) (w : WordInstance) (l : Letter (2*w.particles)) (t : ℕ)
    (rest out : BitString) (height : ℕ) :
    emitLetter.Executes g (state w t rest (kindBits l.kind) (List.replicate l.index.val true) out height)
      (state w t rest [] [] ((pairStream (sampleLetter l t)).reverse++out) (height+t+1)) (12*l.index.val+41*t+67) := by
  apply rename_executes_to SampleAtom.program atomEmbedding g (SampleAtom.program_executes g l t out height)
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | exact (hi 3 rfl).elim | exact (hi 4 rfl).elim

lemma body_executes (g : BitString → ℕ) (w : WordInstance) (l : Letter (2*w.particles)) (t : ℕ)
    (rest out : BitString) (height : ℕ) :
    body.Executes g (state w t (pairBits (letterBits l) rest) [] [] out height)
      (state w t rest [] [] ((pairStream (sampleLetter l t)).reverse++out) (height+t+1)) (17*l.index.val+41*t+120) := by
  convert seq_executes _ _ g (parseLetter_executes g w l t rest out height)
    (emitLetter_executes g w l t rest out height) using 1 <;> omega
end HiddenCircuits.GraphReduction.Runtime.WordGraph.WordSample
