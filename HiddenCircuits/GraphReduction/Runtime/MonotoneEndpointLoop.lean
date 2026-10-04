import HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointCell

namespace HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointRuntime
open Complexity OracleBlock
set_option maxHeartbeats 1000000

noncomputable def candidateLoop : OracleBlock 69 := whilePop 6 candidate candidate
def runCandidates (R : List VertexRecord) (k : ℕ) : ℕ→ℕ→Accum→Accum
  | _,0,A=>A
  | i,m+1,A=>runCandidates R k (i+1) m (step R i k A)
lemma candidates_loop (g : BitString→ℕ) (R : List VertexRecord) (i k m : ℕ)
    (ranks : BitString) (A : Accum) (hi:i+m≤R.length) (hk:k≤R.length) :
    ∃c,WhileExecution (6:Fin 70) candidate candidate g
      (state R i k (List.replicate m true) ranks A)
      (state R (i+m) k [] ranks (runCandidates R k i m A)) c ∧
      c≤m*(cellBound R.length (encodeBitList (R.map encodeVertex)).length+2)+1 := by
  induction m generalizing i A with
  | zero => exact ⟨1,by simpa [runCandidates] using WhileExecution.empty (stack:=(6:Fin 70)) (B:=candidate) (C:=candidate) (g:=g) (state R i k [] ranks A) rfl,by simp⟩
  | succ m ih =>
    obtain ⟨a,ha,hab⟩:=candidate_executes g R i k (List.replicate m true) ranks A (by omega) hk
    obtain ⟨b,hb,hbb⟩:=ih (i+1) (step R i k A) (by omega)
    have hu:Function.update (state R i k (List.replicate (m+1) true) ranks A) (6:Fin 70) (List.replicate m true)=
        state R i k (List.replicate m true) ranks A:=by funext j;fin_cases j <;> rfl
    have he:=WhileExecution.one (stack:=(6:Fin 70)) (B:=candidate) (C:=candidate) (g:=g)
      (show (state R i k (List.replicate (m+1) true) ranks A) 6=true::List.replicate m true from rfl)
      (by rw[hu];exact ha) hb
    refine ⟨1+a+1+b,?_,by nlinarith⟩
    convert he using 1 <;> simp [runCandidates,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

noncomputable def rankRow : OracleBlock 69 := seq (copyOn 0 6 7 (by decide) (by decide) (by decide))
  (seq candidateLoop (seq (clear 1) (push 57 true)))
noncomputable def rankLoop : OracleBlock 69 := whilePop 58 rankRow rankRow
def runRanks (R : List VertexRecord) : ℕ→ℕ→Accum→Accum
  | _,0,A=>A
  | k,m+1,A=>runRanks R (k+1) m (runCandidates R k 0 R.length A)
def rowBound (n L : ℕ) := n*(cellBound n L+8)+11
lemma rankRow_executes (g : BitString→ℕ) (R : List VertexRecord) (k : ℕ)
    (ranks : BitString) (A : Accum) (hk:k≤R.length) :
    ∃c,rankRow.Executes g (state R 0 k [] ranks A)
      (state R 0 (k+1) [] ranks (runCandidates R k 0 R.length A)) c ∧
      c≤rowBound R.length (encodeBitList (R.map encodeVertex)).length := by
  have h₁:(copyOn (0:Fin 70) 6 7 (by decide) (by decide) (by decide)).Executes g (state R 0 k [] ranks A)
      (state R 0 k (List.replicate R.length true) ranks A) (5*R.length+2):=by
    convert copyOn_executes g (0:Fin 70) 6 7 (by decide) (by decide) (by decide) (state R 0 k [] ranks A) rfl using 1
    · funext j;fin_cases j <;> simp [state,combine,MatrixEmitter.store,MatrixEmitter.port]
    · simp [state,combine,MatrixEmitter.store,MatrixEmitter.port]
  obtain ⟨c,hc,hb⟩:=candidates_loop g R 0 k R.length ranks A (by omega) hk
  have h₂:=whilePop_executes _ _ _ g hc
  simp only [Nat.zero_add] at h₂
  have h₃:(clear (1:Fin 70)).Executes g (state R R.length k [] ranks (runCandidates R k 0 R.length A))
      (state R 0 k [] ranks (runCandidates R k 0 R.length A)) (R.length+1):=by
    convert clear_executes g (1:Fin 70) (state R R.length k [] ranks (runCandidates R k 0 R.length A)) using 1
    · funext j;fin_cases j <;> rfl
    · simp [state,combine,MatrixEmitter.store,MatrixEmitter.port]
  have h₄:(push (57:Fin 70) true).Executes g (state R 0 k [] ranks (runCandidates R k 0 R.length A))
      (state R 0 (k+1) [] ranks (runCandidates R k 0 R.length A)) 1:=by
    convert push_executes g (57:Fin 70) true (state R 0 k [] ranks (runCandidates R k 0 R.length A)) using 1
    funext j;fin_cases j <;> simp [state,combine,high,List.replicate_succ]
  refine ⟨_,seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ h₄)),?_⟩
  unfold rowBound
  nlinarith
lemma ranks_loop (g : BitString→ℕ) (R : List VertexRecord) (k m : ℕ)
    (A : Accum) (hk:k+m≤R.length) :
    ∃c,WhileExecution (58:Fin 70) rankRow rankRow g (state R 0 k [] (List.replicate m true) A)
      (state R 0 (k+m) [] [] (runRanks R k m A)) c ∧
      c≤m*(rowBound R.length (encodeBitList (R.map encodeVertex)).length+2)+1 := by
  induction m generalizing k A with
  | zero => exact ⟨1,by simpa [runRanks] using WhileExecution.empty (stack:=(58:Fin 70)) (B:=rankRow) (C:=rankRow) (g:=g) (state R 0 k [] [] A) rfl,by simp⟩
  | succ m ih =>
    obtain ⟨a,ha,hab⟩:=rankRow_executes g R k (List.replicate m true) A (by omega)
    obtain ⟨b,hb,hbb⟩:=ih (k+1) (runCandidates R k 0 R.length A) (by omega)
    have hu:Function.update (state R 0 k [] (List.replicate (m+1) true) A) (58:Fin 70) (List.replicate m true)=
        state R 0 k [] (List.replicate m true) A:=by funext j;fin_cases j <;> rfl
    have he:=WhileExecution.one (stack:=(58:Fin 70)) (B:=rankRow) (C:=rankRow) (g:=g)
      (show (state R 0 k [] (List.replicate (m+1) true) A) 58=true::List.replicate m true from rfl)
      (by rw[hu];exact ha) hb
    refine ⟨1+a+1+b,?_,by nlinarith⟩
    convert he using 1 <;> simp [runRanks,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
lemma rankLoop_queryFree : rankLoop.QueryFree :=
  whilePop_queryFree _ _ _
    (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _
      (whilePop_queryFree _ _ _ candidate_queryFree candidate_queryFree)
      (seq_queryFree _ _ (clear_queryFree _) (push_queryFree _ _))))
    (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _
      (whilePop_queryFree _ _ _ candidate_queryFree candidate_queryFree)
      (seq_queryFree _ _ (clear_queryFree _) (push_queryFree _ _))))
end HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointRuntime
