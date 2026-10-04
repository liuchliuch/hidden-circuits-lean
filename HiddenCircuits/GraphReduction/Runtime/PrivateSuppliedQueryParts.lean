import HiddenCircuits.GraphReduction.Runtime.PrivateRankEmitter
import HiddenCircuits.GraphReduction.Runtime.CliqueEmitter
import HiddenCircuits.GraphReduction.Runtime.TripleSerialization
import HiddenCircuits.Complexity.OracleMove

namespace HiddenCircuits.GraphReduction.Runtime.PrivateSuppliedQuery
open Complexity OracleBlock BinaryArithmetic Polynomial
set_option maxHeartbeats 900000

def state (n : ℕ) (desc output graph upper lower : BitString) : Store 63 := fun i =>
  if i.val=0 then List.replicate n true else if i.val=7 then output else if i.val=8 then desc
  else if i.val=57 then graph else if i.val=58 then upper else if i.val=59 then lower else []
def embedding : Fin 57 ↪ Fin 64 := Fin.castAddEmb 7
def tripleEmbedding : Fin 8 ↪ Fin 64 where
  toFun i := (![57,58,59,60,61,62,7,63] : Fin 8 → Fin 64) i
  inj' := by decide +kernel
noncomputable def graph : OracleBlock 63 := rename (CliqueEmitter.program true) embedding
noncomputable def rank (lower : Bool) : OracleBlock 63 := rename (PrivateRankEmitter.program lower) embedding
noncomputable def saveGraph : OracleBlock 63 := moveOn 7 57 58 (by decide) (by decide) (by decide)
noncomputable def saveUpper : OracleBlock 63 := reverseOn 7 58 (by decide)
noncomputable def saveLower : OracleBlock 63 := reverseOn 7 59 (by decide)
noncomputable def serialize : OracleBlock 63 := rename TripleSerialization.program tripleEmbedding

lemma graph_executes {p h : ℕ} (g : BitString→ℕ) (pairs : Fin h→CutPair p) (S T : State (2*p) p) (s : ℕ) :
    ∃c,graph.Executes g (state (privateGraphInput pairs S T s).1 (privateDescriptor pairs S T s) [] [] [] [])
      (state (privateGraphInput pairs S T s).1 (privateDescriptor pairs S T s) (privateGraphInput pairs S T s).encode [] [] []) c ∧
      c≤CliqueEmitter.time.eval ((privateGraphInput pairs S T s).1+(privateDescriptor pairs S T s).length) := by
  obtain ⟨c,hc,hb⟩:=CliqueEmitter.program_polynomial g true pairs S T s
  refine ⟨c,?_,hb⟩
  apply rename_executes_to (CliqueEmitter.program true) embedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · clear hc hb
    intro i hi
    have h7:i.val≠7:=by intro h;exact hi 7 (Fin.ext h.symm)
    simp only [state,h7,if_false]

lemma rank_executes (g : BitString→ℕ) (lower : Bool) (records : List VertexRecord) (a b c : BitString) :
    ∃t,(rank lower).Executes g (state records.length (encodeBitList (records.map encodeVertex)) [] a b c)
      (state records.length (encodeBitList (records.map encodeVertex)) (PrivateRankEmitter.bits lower records) a b c) t ∧
      t≤PrivateRankEmitter.time.eval (records.length+(encodeBitList (records.map encodeVertex)).length) := by
  obtain ⟨t,ht,hb⟩:=PrivateRankEmitter.program_executes g lower records
  refine ⟨t,?_,hb⟩
  apply rename_executes_to (PrivateRankEmitter.program lower) embedding g ht
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · clear ht hb
    intro i hi
    have h7:i.val≠7:=by intro h;exact hi 7 (Fin.ext h.symm)
    simp only [state,h7,if_false]

lemma saveGraph_executes (g : BitString→ℕ) (n : ℕ) (D G : BitString) :
    saveGraph.Executes g (state n D G [] [] []) (state n D [] G [] []) (6*G.length+5) := by
  convert moveOn_executes g (7:Fin 64) 57 58 (by decide) (by decide) (by decide) (state n D G [] [] []) rfl using 1
  funext i;fin_cases i <;> simp [state]
lemma saveUpper_executes (g : BitString→ℕ) (n : ℕ) (D G U : BitString) :
    saveUpper.Executes g (state n D U G [] []) (state n D [] G U.reverse []) (2*U.length+1) := by
  convert reverseOn_executes g (7:Fin 64) 58 (by decide) (state n D U G [] []) using 1
  funext i;fin_cases i <;> simp [state]
lemma saveLower_executes (g : BitString→ℕ) (n : ℕ) (D G U V : BitString) :
    saveLower.Executes g (state n D V G U []) (state n D [] G U V.reverse) (2*V.length+1) := by
  convert reverseOn_executes g (7:Fin 64) 59 (by decide) (state n D V G U []) using 1
  funext i;fin_cases i <;> simp [state]
lemma serialize_executes (g : BitString→ℕ) (n : ℕ) (D G U V : BitString) :
    serialize.Executes g (state n D [] G U.reverse V.reverse) (state n D (encodeBitList [G,U,V]) [] [] [])
      (10*G.length+12*U.length+12*V.length+46) := by
  apply rename_executes_to TripleSerialization.program tripleEmbedding g (TripleSerialization.program_executes g G U V)
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have h7:i.val≠7:=by intro h;exact hi 6 (Fin.ext h.symm)
    have h57:i.val≠57:=by intro h;exact hi 0 (Fin.ext h.symm)
    have h58:i.val≠58:=by intro h;exact hi 1 (Fin.ext h.symm)
    have h59:i.val≠59:=by intro h;exact hi 2 (Fin.ext h.symm)
    simp only [state,h7,h57,h58,h59,if_false]
end HiddenCircuits.GraphReduction.Runtime.PrivateSuppliedQuery
