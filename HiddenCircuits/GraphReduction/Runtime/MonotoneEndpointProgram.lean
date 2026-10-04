import HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointLoop

namespace HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointRuntime
open Complexity OracleBlock
set_option maxHeartbeats 1000000

def result (R : List VertexRecord) : Accum := runRanks R 0 R.length initialAccum
def computedBits (R : List VertexRecord) : BitString :=
  encodeBitList [List.replicate (result R).count true,(result R).lows.reverse,(result R).highs.reverse]
def initial (R : List VertexRecord) : Store 69 := state R 0 0 [] [] initialAccum
def clean (R : List VertexRecord) (out : BitString) : Store 69 := Function.update (initial R) 7 out
def tripleEmbedding : Fin 8 ↪ Fin 70 where
  toFun i:=(![61,59,60,62,63,64,7,65] : Fin 8→Fin 70) i
  inj':=by decide +kernel
noncomputable def serialize : OracleBlock 69 := rename TripleSerialization.program tripleEmbedding
noncomputable def program : OracleBlock 69 := seq (copyOn 0 58 7 (by decide) (by decide) (by decide))
  (seq rankLoop (seq (clear 57) serialize))
lemma serialize_executes (g : BitString→ℕ) (R : List VertexRecord) (A : Accum) :
    serialize.Executes g (state R 0 0 [] [] A)
      (clean R (encodeBitList [List.replicate A.count true,A.lows.reverse,A.highs.reverse]))
      (10*A.count+12*A.lows.length+12*A.highs.length+46) := by
  have hc:=TripleSerialization.program_executes g (List.replicate A.count true) A.lows.reverse A.highs.reverse
  simp only [List.reverse_reverse,List.length_replicate,List.length_reverse] at hc
  apply rename_executes_to _ tripleEmbedding g hc
  · funext j;fin_cases j <;> rfl
  · funext j;fin_cases j <;> rfl
  · intro j hj
    have h7:j.val≠7:=by intro h;exact hj 6 (Fin.ext h.symm)
    have h59:j.val≠59:=by intro h;exact hj 1 (Fin.ext h.symm)
    have h60:j.val≠60:=by intro h;exact hj 2 (Fin.ext h.symm)
    have h61:j.val≠61:=by intro h;exact hj 0 (Fin.ext h.symm)
    fin_cases j <;> first | rfl | simp_all
lemma program_executes (g : BitString→ℕ) (R : List VertexRecord) :
    ∃c,program.Executes g (initial R) (clean R (computedBits R)) c ∧
      c≤R.length*(rowBound R.length (encodeBitList (R.map encodeVertex)).length+2)+6*R.length+
        10*(result R).count+12*(result R).lows.length+12*(result R).highs.length+56 := by
  have h₁:(copyOn (0:Fin 70) 58 7 (by decide) (by decide) (by decide)).Executes g (initial R)
      (state R 0 0 [] (List.replicate R.length true) initialAccum) (5*R.length+2):=by
    convert copyOn_executes g (0:Fin 70) 58 7 (by decide) (by decide) (by decide) (initial R) rfl using 1
    · funext j;fin_cases j <;> simp [initial,state,combine,high,initialAccum,MatrixEmitter.store,MatrixEmitter.port]
    · simp [initial,state,combine,high,initialAccum,MatrixEmitter.store,MatrixEmitter.port]
  obtain ⟨c,hc,hb⟩:=ranks_loop g R 0 R.length initialAccum (by omega)
  have h₂:=whilePop_executes _ _ _ g hc
  simp only [Nat.zero_add] at h₂
  have h₃:(clear (57:Fin 70)).Executes g (state R 0 R.length [] [] (result R))
      (state R 0 0 [] [] (result R)) (R.length+1):=by
    convert clear_executes g (57:Fin 70) (state R 0 R.length [] [] (result R)) using 1
    · funext j;fin_cases j <;> rfl
    · simp [state,combine,high]
  exact ⟨_,seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ (serialize_executes g R (result R)))),by omega⟩
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ rankLoop_queryFree (seq_queryFree _ _ (clear_queryFree _) (rename_queryFree _ _ TripleSerialization.program_queryFree)))
end HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointRuntime
