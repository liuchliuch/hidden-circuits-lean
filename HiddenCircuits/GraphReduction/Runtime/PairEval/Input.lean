import HiddenCircuits.Complexity.PairEncoding
import HiddenCircuits.GraphReduction.Runtime.WordGraph.WordParserCorrectness

/-! Literal parsing of the standalone pair input into physical unary dimensions,
its two independent boundary masks and the original ordered pair stream. -/
namespace HiddenCircuits.GraphReduction.Runtime.PairEval.Input
open Complexity OracleBlock WordGraph
noncomputable abbrev program := WordParser.program

def state (w : PairInput) (sample : ℕ) : Store 17 := WordParser.store (pairInputBits w)
  (List.replicate w.particles true) (stateBits w.source) (stateBits w.target)
  (pairStream w.pairs) (List.replicate w.pairs.length true) (List.replicate sample true)

theorem program_executes (g : BitString→ℕ) (w : PairInput) (sample : ℕ) :
    ∃c,program.Executes g (WordParser.store (pairInputBits w) [] [] [] [] [] (List.replicate sample true))
      (state w sample) c ∧ c≤40*(pairInputBits w).length+100 := by
  simpa only [state,pairInputBits,pairStream,List.length_map] using
    WordParser.program_raw g w.particles (stateBits w.source) (stateBits w.target) (w.pairs.map pairAtom) (List.replicate sample true)
lemma program_queryFree : program.QueryFree := WordParser.program_queryFree
end HiddenCircuits.GraphReduction.Runtime.PairEval.Input
