import HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointValues

namespace HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointRuntime
open Complexity OracleBlock
set_option maxHeartbeats 1200000

def rankEmbedding : Fin 6 ↪ Fin 70 where
  toFun i:=(![4,57,64,65,66,67] : Fin 6→Fin 70) i
  inj':=by decide +kernel
noncomputable def compareRank : OracleBlock 69 := GraphVerifier.Runtime.readLengthOn rankEmbedding
noncomputable def selectValues : OracleBlock 69 := branchPop 3 (clear 64) (clear 64) (branchPop 64 skip skip values)
noncomputable def candidate : OracleBlock 69 := seq (countProgram false false) (seq compareRank (seq (clear 4)
  (seq leftProgram (seq selectValues (push 1 true)))))
def selected (R : List VertexRecord) (i k : ℕ) : Bool :=
  !(R[i]?.getD defaultRecord).side && decide (countValue false false R i=k)
def step (R : List VertexRecord) (i k : ℕ) (A : Accum) : Accum :=
  if selected R i k then emitValues A (countValue false true R i) (countValue true true R i) else A
def cellBound (n L : ℕ) := 3*countBound n L+MonotoneOrderRuntime.bound n L+100*n+200

lemma compareRank_executes (g : BitString→ℕ) (R : List VertexRecord) (i k : ℕ)
    (candidates ranks : BitString) (A : Accum) (v : ℕ) :
    ∃c,compareRank.Executes g (state R i k candidates ranks A (List.replicate v true))
      (state R i k candidates ranks A (List.replicate v true) [] [] [decide (v=k)]) c ∧ c≤13*(v+k)+23 := by
  obtain ⟨c,hc,hb⟩:=GraphVerifier.Runtime.readLengthOn_executes rankEmbedding g
    (state R i k candidates ranks A (List.replicate v true)) (List.replicate v true) (List.replicate k true)
    (by funext j;fin_cases j <;> rfl)
  simp only [List.length_replicate] at hc hb
  refine ⟨c,?_,hb⟩
  convert hc using 1
  funext j;fin_cases j <;> rfl
lemma clearCount_executes (g : BitString→ℕ) (R : List VertexRecord) (i k : ℕ)
    (candidates ranks : BitString) (A : Accum) (v : ℕ) (flag : BitString) :
    (clear (4:Fin 70)).Executes g (state R i k candidates ranks A (List.replicate v true) [] [] flag)
      (state R i k candidates ranks A [] [] [] flag) (v+1) := by
  convert clear_executes g (4:Fin 70) (state R i k candidates ranks A (List.replicate v true) [] [] flag) using 1
  · funext j;fin_cases j <;> rfl
  · simp [state,combine,MatrixEmitter.store,MatrixEmitter.port]
lemma selectValues_executes (g : BitString→ℕ) (R : List VertexRecord) (i k : ℕ)
    (candidates ranks : BitString) (A : Accum) (hi:i<R.length) :
    ∃c,selectValues.Executes g
      (state R i k candidates ranks A [] [] [] [decide (countValue false false R i=k)] [!(R[i]?.getD defaultRecord).side])
      (state R i k candidates ranks (step R i k A)) c ∧
      c≤2*countBound R.length (encodeBitList (R.map encodeVertex)).length+44*R.length+62 := by
  let eq:=decide (countValue false false R i=k)
  let left:=!(R[i]?.getD defaultRecord).side
  let start:=state R i k candidates ranks A [] [] [] [eq] [left]
  have hu:Function.update start (3:Fin 70) []=state R i k candidates ranks A [] [] [] [eq]:=by funext j;fin_cases j <;> rfl
  have hv:Function.update (state R i k candidates ranks A [] [] [] [eq]) (64:Fin 70) []=state R i k candidates ranks A:=by funext j;fin_cases j <;> rfl
  cases hl:left with
  | false =>
    have he:step R i k A=A:=by
      change (if left && eq then _ else _)=_
      simp [hl]
    have hc:(clear (64:Fin 70)).Executes g (state R i k candidates ranks A [] [] [] [eq]) (state R i k candidates ranks A) 2:=by
      simpa only [hv] using clear_executes g (64:Fin 70) (state R i k candidates ranks A [] [] [] [eq])
    refine ⟨4,?_,by omega⟩
    rw [he]
    apply branchPop_false _ _ _ _ g (by change [left]=false::[];rw[hl])
    rw [hu];exact hc
  | true =>
    cases hq:eq with
    | false =>
      have he:step R i k A=A:=by
        change (if left && eq then _ else _)=_
        simp [hl,hq]
      refine ⟨5,?_,by omega⟩
      rw [he]
      apply branchPop_true _ _ _ _ g (by change [left]=true::[];rw[hl])
      rw [hu]
      apply branchPop_false _ _ _ _ g (by change [eq]=false::[];rw[hq])
      rw [hv];exact skip_executes _ _
    | true =>
      have he:step R i k A=emitValues A (countValue false true R i) (countValue true true R i):=by
        change (if left && eq then _ else _)=_
        simp [hl,hq]
      obtain ⟨c,hc,hb⟩:=values_executes g R i k candidates ranks A hi
      refine ⟨c+4,?_,by omega⟩
      rw [he]
      apply branchPop_true _ _ _ _ g (by change [left]=true::[];rw[hl])
      rw [hu]
      apply branchPop_true _ _ _ _ g (by change [eq]=true::[];rw[hq])
      rw [hv];exact hc

lemma candidate_executes (g : BitString→ℕ) (R : List VertexRecord) (i k : ℕ)
    (candidates ranks : BitString) (A : Accum) (hi:i<R.length) (hk:k≤R.length) :
    ∃c,candidate.Executes g (state R i k candidates ranks A)
      (state R (i+1) k candidates ranks (step R i k A)) c ∧ c≤cellBound R.length (encodeBitList (R.map encodeVertex)).length := by
  obtain ⟨a,ha,hab⟩:=count_executes g false false R i k candidates ranks A [] [] hi
  obtain ⟨b,hb,hbb⟩:=compareRank_executes g R i k candidates ranks A (countValue false false R i)
  have hc:=clearCount_executes g R i k candidates ranks A (countValue false false R i) [decide (countValue false false R i=k)]
  obtain ⟨d,hd,hdb⟩:=left_executes g R i k candidates ranks A [decide (countValue false false R i=k)] hi
  obtain ⟨e,he,heb⟩:=selectValues_executes g R i k candidates ranks A hi
  have hf:(push (1:Fin 70) true).Executes g (state R i k candidates ranks (step R i k A))
      (state R (i+1) k candidates ranks (step R i k A)) 1:=by
    convert push_executes g (1:Fin 70) true (state R i k candidates ranks (step R i k A)) using 1
    funext j;fin_cases j <;> simp [state,combine,MatrixEmitter.store,MatrixEmitter.port,List.replicate_succ]
  have hv:=countValue_le false false R i
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb (seq_executes _ _ g hc (seq_executes _ _ g hd (seq_executes _ _ g he hf)))),?_⟩
  unfold cellBound
  omega
lemma candidate_queryFree : candidate.QueryFree := seq_queryFree _ _ (count_queryFree _ _)
  (seq_queryFree _ _ (GraphVerifier.Runtime.readLengthOn_queryFree _) (seq_queryFree _ _ (clear_queryFree _)
    (seq_queryFree _ _ left_queryFree (seq_queryFree _ _
      (branchPop_queryFree _ _ _ _ (clear_queryFree _) (clear_queryFree _)
        (branchPop_queryFree _ _ _ _ skip_queryFree skip_queryFree values_queryFree)) (push_queryFree _ _)))))
end HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointRuntime
