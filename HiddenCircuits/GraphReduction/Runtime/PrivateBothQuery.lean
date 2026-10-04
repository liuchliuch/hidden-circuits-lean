import HiddenCircuits.GraphReduction.Runtime.PrivateBothQueryParts

namespace HiddenCircuits.GraphReduction.Runtime.PrivateBothQuery
open Complexity OracleBlock Polynomial
open PrivateSuppliedQuery (state saveGraph saveUpper saveLower serialize
  saveGraph_executes saveUpper_executes saveLower_executes serialize_executes)
set_option maxHeartbeats 1000000

noncomputable def program : OracleBlock 63 := seq PrivateSuppliedQuery.program (seq saveGraph (seq (rank true)
  (seq saveUpper (seq (rank false) (seq saveLower serialize)))))
noncomputable def time : Polynomial ℕ := 150000*(X+1)^4

lemma suppliedBits_length {p h : ℕ} (pairs : Fin h→CutPair p) (S T : State (2*p) p) (s : ℕ) :
    (PrivateSuppliedQuery.bits pairs S T s).length≤10*(privateGraphInput pairs S T s).1^2+12*(privateGraphInput pairs S T s).1+8 := by
  let R:=privateRecords pairs S T s
  have hR:=privateRecords_length pairs S T s
  have hu:=PrivateSuppliedQuery.bits_length_rank false R
  have hv:=PrivateSuppliedQuery.bits_length_rank true R
  have hG:=GraphInput.encode_length (privateGraphInput pairs S T s)
  have hp:PrivateSuppliedQuery.bits pairs S T s=encodeBitList
      [(privateGraphInput pairs S T s).encode,PrivateRankEmitter.bits false R,PrivateRankEmitter.bits true R]:=by
    dsimp only [R,PrivateSuppliedQuery.bits]
    rw [PrivateRankEmitter.upper_bits_correct,PrivateRankEmitter.lower_bits_correct]
  dsimp only [R] at hu hv
  rw [hR] at hu hv
  rw [hp]
  simp only [encodeBitList,List.length_cons,pairBits_length,List.length_nil]
  nlinarith

theorem program_executes {p h : ℕ} (g : BitString→ℕ) (pairs : Fin h→CutPair p) (S T : State (2*p) p) (s : ℕ) :
    ∃c,program.Executes g (state (privateGraphInput pairs S T s).1 (privateDescriptor pairs S T s) [] [] [] [])
      (state (privateGraphInput pairs S T s).1 (privateDescriptor pairs S T s) (bits pairs S T s) [] [] []) c ∧
      c≤time.eval ((privateGraphInput pairs S T s).1+(privateDescriptor pairs S T s).length) := by
  let N:=(privateGraphInput pairs S T s).1
  let D:=privateDescriptor pairs S T s
  let G:=PrivateSuppliedQuery.bits pairs S T s
  let R:=privateRecords pairs S T s
  let U:=PrivateIntervalEmitter.bits true R
  let V:=PrivateIntervalEmitter.bits false R
  have hN:R.length=N:=privateRecords_length pairs S T s
  have hD:encodeBitList (R.map encodeVertex)=D:=rfl
  obtain ⟨a,ha,hab⟩:=PrivateSuppliedQuery.program_executes g pairs S T s
  obtain ⟨b,hb,hbb⟩:=rank_executes g true R G [] []
  obtain ⟨c,hc,hcb⟩:=rank_executes g false R G U.reverse []
  rw [hN,hD] at hb hbb hc hcb
  have he:=seq_executes _ _ g ha (seq_executes _ _ g (saveGraph_executes g N D G)
    (seq_executes _ _ g hb (seq_executes _ _ g (saveUpper_executes g N D G U)
      (seq_executes _ _ g hc (seq_executes _ _ g (saveLower_executes g N D G U.reverse V)
        (serialize_executes g N D G U V))))))
  have hout:encodeBitList [G,U,V]=bits pairs S T s:=by
    rfl
  rw [hout] at he
  refine ⟨_,he,?_⟩
  have hU:U.length≤2*N^2+2*N:=by simpa only [hN] using intervalBits_length true R
  have hV:V.length≤2*N^2+2*N:=by simpa only [hN] using intervalBits_length false R
  have hG:G.length≤10*N^2+12*N+8:=suppliedBits_length pairs S T s
  have hn:N≤N+D.length:=Nat.le_add_right _ _
  have hsum:a+b+c≤140000*(N+D.length+1)^4:=by
    simp only [PrivateSuppliedQuery.time,PrivateIntervalEmitter.time,eval_mul,eval_pow,eval_add,eval_X,eval_ofNat,eval_one] at hab hbb hcb
    dsimp only [N,D] at *
    omega
  have hcost:a+(6*G.length+5+(b+(2*U.length+1+(c+(2*V.length+1+(10*G.length+12*U.length+12*V.length+46)+2)+2)+2)+2)+2)+2
      ≤140000*(N+D.length+1)^4+216*N^2+248*N+193:=by nlinarith
  refine hcost.trans ?_
  calc
    _≤140000*(N+D.length+1)^4+216*(N+D.length)^2+248*(N+D.length)+193:=by gcongr
    _≤time.eval (N+D.length):=by
      simp only [time,eval_mul,eval_pow,eval_add,eval_X,eval_ofNat,eval_one]
      ring_nf
      omega

lemma program_queryFree : program.QueryFree := seq_queryFree _ _
  PrivateSuppliedQuery.program_queryFree
  (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (rename_queryFree _ _ (PrivateIntervalEmitter.program_queryFree true))
      (seq_queryFree _ _ (reverseOn_queryFree _ _ _)
        (seq_queryFree _ _ (rename_queryFree _ _ (PrivateIntervalEmitter.program_queryFree false))
          (seq_queryFree _ _ (reverseOn_queryFree _ _ _)
            (rename_queryFree _ _ TripleSerialization.program_queryFree))))))
end HiddenCircuits.GraphReduction.Runtime.PrivateBothQuery
