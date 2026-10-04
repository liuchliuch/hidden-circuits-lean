import HiddenCircuits.GraphReduction.Runtime.WordGraph.MonotoneEndpointAnswerCore

namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.MonotoneEndpointAnswer
open Complexity OracleBlock BinaryArithmetic Polynomial
set_option maxHeartbeats 1000000

def store (input : BitString) (t s : ℕ) (answer : BitString) : Store 123 := fun i=>
  if i.val=0 then input else if i.val=1 then List.replicate t true else if i.val=2 then List.replicate s true else if i.val=3 then answer else []
def embedding : Fin 99 ↪ Fin 124 := Fin.castAddEmb 25
noncomputable def program : OracleBlock 123 := rename MonotoneEndpointAnswerCore.program embedding
noncomputable def time : Polynomial ℕ := MonotoneEndpointAnswerCore.time
abbrev queryBits := MonotoneEndpointWordQuery.queryBits
lemma program_polynomial (g : BitString→ℕ) (w : WordInstance) (t s : ℕ) :
    ∃c,program.Executes g (store (wordBits w) t s [])
      (store (wordBits w) t s (signedBits (g (queryBits w t s):ℤ))) c ∧
      c≤time.eval ((wordBits w).length+t+s+(signedBits (g (queryBits w t s):ℤ)).length) := by
  obtain ⟨c,hc,hb⟩:=MonotoneEndpointAnswerCore.program_polynomial g w t s
  refine ⟨c,?_,hb⟩
  apply rename_executes_to _ embedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have h3:i.val≠3:=by intro h;exact hi 3 (Fin.ext h.symm)
    simp only [store,h3,if_false]
end HiddenCircuits.GraphReduction.Runtime.WordGraph.MonotoneEndpointAnswer
