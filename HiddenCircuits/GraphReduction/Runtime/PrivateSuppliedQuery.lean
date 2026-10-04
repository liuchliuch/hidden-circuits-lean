import HiddenCircuits.GraphReduction.Runtime.PrivateSuppliedQueryParts
import HiddenCircuits.GraphReduction.Runtime.PrivateRankCorrect

namespace HiddenCircuits.GraphReduction.Runtime.PrivateSuppliedQuery
open Complexity OracleBlock Polynomial
set_option maxHeartbeats 1000000

def bits {p h : ℕ} (pairs : Fin h→CutPair p) (S T : State (2*p) p) (s : ℕ) : BitString :=
  encodeBitList [(privateGraphInput pairs S T s).encode,
    encodeBitList (List.ofFn (fun i=>List.replicate ((privateMatrixDiagram pairs S T s).upper i) true)),
    encodeBitList (List.ofFn (fun i=>List.replicate ((privateMatrixDiagram pairs S T s).lower i) true))]
noncomputable def program : OracleBlock 63 := seq graph (seq saveGraph (seq (rank false)
  (seq saveUpper (seq (rank true) (seq saveLower serialize)))))
noncomputable def time : Polynomial ℕ := 60000*(X+1)^4

lemma bits_length_rank (lower : Bool) (R : List VertexRecord) :
    (PrivateRankEmitter.bits lower R).length≤2*R.length^2+2*R.length := by
  simpa only [PrivateRankEmitter.bits,pow_two,Nat.mul_assoc] using RankEmitter.bits_length_bound R.length (PrivateRankEmitter.edge lower R)

theorem program_executes {p h : ℕ} (g : BitString→ℕ) (pairs : Fin h→CutPair p) (S T : State (2*p) p) (s : ℕ) :
    ∃c,program.Executes g (state (privateGraphInput pairs S T s).1 (privateDescriptor pairs S T s) [] [] [] [])
      (state (privateGraphInput pairs S T s).1 (privateDescriptor pairs S T s) (bits pairs S T s) [] [] []) c ∧
      c≤time.eval ((privateGraphInput pairs S T s).1+(privateDescriptor pairs S T s).length) := by
  let N:=(privateGraphInput pairs S T s).1
  let D:=privateDescriptor pairs S T s
  let G:=(privateGraphInput pairs S T s).encode
  let R:=privateRecords pairs S T s
  let U:=PrivateRankEmitter.bits false R
  let V:=PrivateRankEmitter.bits true R
  have hN:R.length=N:=privateRecords_length pairs S T s
  have hD:encodeBitList (R.map encodeVertex)=D:=rfl
  obtain ⟨a,ha,hab⟩:=graph_executes g pairs S T s
  obtain ⟨b,hb,hbb⟩:=rank_executes g false R G [] []
  obtain ⟨c,hc,hcb⟩:=rank_executes g true R G U.reverse []
  rw [hN,hD] at hb hbb hc hcb
  have he:=seq_executes _ _ g ha (seq_executes _ _ g (saveGraph_executes g N D G)
    (seq_executes _ _ g hb (seq_executes _ _ g (saveUpper_executes g N D G U)
      (seq_executes _ _ g hc (seq_executes _ _ g (saveLower_executes g N D G U.reverse V)
        (serialize_executes g N D G U V))))))
  have hout:encodeBitList [G,U,V]=bits pairs S T s:=by
    dsimp only [G,U,V,R,bits]
    rw [PrivateRankEmitter.upper_bits_correct,PrivateRankEmitter.lower_bits_correct]
  rw [hout] at he
  refine ⟨_,he,?_⟩
  have hU:U.length≤2*N^2+2*N:=by simpa only [hN] using bits_length_rank false R
  have hV:V.length≤2*N^2+2*N:=by simpa only [hN] using bits_length_rank true R
  have hG:G.length=2*N+N*N+1:=GraphInput.encode_length _
  have hn:N≤N+D.length:=Nat.le_add_right _ _
  have hsum:a+b+c≤50000*(N+D.length+1)^4:=by
    simp only [CliqueEmitter.time,PrivateRankEmitter.time,eval_mul,eval_pow,eval_add,eval_X,eval_ofNat,eval_one] at hab hbb hcb
    dsimp only [N,D] at *
    omega
  have hcost:a+(6*G.length+5+(b+(2*U.length+1+(c+(2*V.length+1+(10*G.length+12*U.length+12*V.length+46)+2)+2)+2)+2)+2)+2
      ≤50000*(N+D.length+1)^4+72*N^2+88*N+81:=by nlinarith
  refine hcost.trans ?_
  calc
    _≤50000*(N+D.length+1)^4+72*(N+D.length)^2+88*(N+D.length)+81:=by gcongr
    _≤time.eval (N+D.length):=by
      simp only [time,eval_mul,eval_pow,eval_add,eval_X,eval_ofNat,eval_one]
      ring_nf
      omega

lemma program_queryFree : program.QueryFree := seq_queryFree _ _
  (rename_queryFree _ _ (CliqueEmitter.program_queryFree true))
  (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (rename_queryFree _ _ (PrivateRankEmitter.program_queryFree false))
      (seq_queryFree _ _ (reverseOn_queryFree _ _ _)
        (seq_queryFree _ _ (rename_queryFree _ _ (PrivateRankEmitter.program_queryFree true))
          (seq_queryFree _ _ (reverseOn_queryFree _ _ _)
            (rename_queryFree _ _ TripleSerialization.program_queryFree))))))
end HiddenCircuits.GraphReduction.Runtime.PrivateSuppliedQuery
