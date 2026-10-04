import HiddenCircuits.GraphReduction.Runtime.PairEval.DriverPorts
import HiddenCircuits.GraphReduction.Runtime.PairEval.GraphAnswer
import HiddenCircuits.GraphReduction.Runtime.PairEval.CliqueAnswer

/-! Each loop cell issues its single physically emitted graph query. The
private supplied mode emits its promised representation in the query itself. -/
namespace HiddenCircuits.GraphReduction.Runtime.PairEval.Driver
open Complexity OracleBlock BinaryArithmetic Polynomial WordGraph
set_option maxHeartbeats 900000
abbrev Target := Option CliqueFrontend.Kind
def modelKind : Target → GraphRecovery.Kind
  | none => none
  | some k => some (CliqueFrontend.mode k)
def queryBits (kind : Target) (w : PairInput) (s : ℕ) : BitString :=
  match kind with
  | none => GraphFrontend.queryBits w 0 s
  | some k => CliqueFrontend.queryBits k w 0 s
noncomputable def queryProgram : Target → OracleBlock 85
  | none => GraphAnswer.program
  | some k => CliqueAnswer.program k
noncomputable def queryTime : Target → Polynomial ℕ
  | none => GraphAnswer.time
  | some k => CliqueAnswer.time k
noncomputable def queryCell (kind : Target) : OracleBlock 97 := rename (queryProgram kind) queryEmbedding

def answerValue (kind : Target) (g : BitString→ℕ) (w : PairInput) (s : GraphRecovery.Index w) : ℕ := g (queryBits kind w s.val)
def CorrectOracle (kind : Target) (g : BitString→ℕ) (w : PairInput) : Prop :=
  ∀s,answerValue kind g w s=perfectMatchingCount (GraphRecovery.query (modelKind kind) w s).2.graph

lemma queryProgram_executes (kind : Target) (g : BitString→ℕ) (w : PairInput) (s : ℕ) :
    ∃c,(queryProgram kind).Executes g (GraphAnswer.store (pairInputBits w) 0 s [])
      (GraphAnswer.store (pairInputBits w) 0 s (signedBits (g (queryBits kind w s):ℤ))) c ∧
      c ≤ (queryTime kind).eval ((pairInputBits w).length+s+(signedBits (g (queryBits kind w s):ℤ)).length) := by
  cases kind with
  | none => simpa only [Nat.add_zero] using GraphAnswer.program_polynomial g w 0 s
  | some k => simpa only [Nat.add_zero] using CliqueAnswer.program_polynomial k g w 0 s

lemma queryCell_executes (kind : Target) (g : BitString→ℕ) (w : PairInput) (s : GraphRecovery.Index w) (a : ℤ×ℤ) :
    ∃c,(queryCell kind).Executes g (state w (degree w-s.val) s.val a [] [] [])
      (state w (degree w-s.val) s.val a (signedBits (answerValue kind g w s:ℤ)) [] []) c ∧
      c ≤ (queryTime kind).eval ((pairInputBits w).length+s.val+(signedBits (answerValue kind g w s:ℤ)).length) := by
  obtain ⟨c,hc,hb⟩ := queryProgram_executes kind g w s.val
  refine ⟨c,?_,hb⟩
  apply rename_executes_to (queryProgram kind) queryEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have h12 : i.val≠12 := by intro h;exact hi 3 (Fin.ext h.symm)
    simp only [state,h12,if_false]
end HiddenCircuits.GraphReduction.Runtime.PairEval.Driver
