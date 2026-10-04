import HiddenCircuits.DH.Runtime.PairCheckModel

/-! A literal three-adjacency umbrella-cell checker. Nested tail scans will
supply the three labels in increasing list-position order; no supplied order
certificate or primitive graph predicate is used by the machine. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRecognitionUmbrella
open Complexity Complexity.OracleBlock DH.Runtime.PairCheck

def cell {n : ℕ} (G : MatrixData n) (u v w : Fin n) : Bool :=
  !G.edge u w || (G.edge u v && G.edge v w)

def words {n : ℕ} (ls : List (Fin n)) : List BitString := ls.map (fun v=>List.replicate v.val true)
def encoded {n : ℕ} (ls : List (Fin n)) : BitString := encodeBitList (words ls)

def state (n u v w : ℕ) (payload original outer middle inner acc uw uv vw out flag : BitString) : Store 18 :=
  fun r => if r.val=0 then List.replicate n true else if r.val=1 then payload
    else if r.val=2 then original else if r.val=3 then acc else if r.val=4 then outer
    else if r.val=5 then middle else if r.val=6 then inner else if r.val=7 then List.replicate u true
    else if r.val=8 then List.replicate v true else if r.val=9 then List.replicate w true
    else if r.val=10 then uw else if r.val=11 then uv else if r.val=12 then vw
    else if r.val=13 then out else if r.val=18 then flag else []

def edgeEmbedding (which : Fin 3) : Fin 9 ↪ Fin 19 where
  toFun i := ![0,if which.val=2 then 8 else 7,if which.val=1 then 8 else 9,1,
    if which.val=0 then 10 else if which.val=1 then 11 else 12,14,15,16,17] i
  inj' := by fin_cases which <;> decide +kernel
noncomputable def readEdge (which : Fin 3) : OracleBlock 18 := GraphVerifier.Runtime.matrixLookupOn (edgeEmbedding which)

def decisionValue : List Bool → Bool
  | [acc,uw,uv,vw] => acc && (!uw || (uv && vw))
  | _ => false
noncomputable def cellProgram : OracleBlock 18 := seq (readEdge 0) (seq (readEdge 1)
  (seq (readEdge 2) (seq (GraphVerifier.Runtime.decision 13 [3,10,11,12] decisionValue)
    (reverseOn 13 3 (by decide)))))

theorem cellProgram_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (u v w : Fin n) (original outer middle inner : BitString) (acc : Bool) :
    ∃t, cellProgram.Executes g (state n u.val v.val w.val G.bits original outer middle inner [acc] [] [] [] [] [])
      (state n u.val v.val w.val G.bits original outer middle inner [acc && cell G u v w] [] [] [] [] []) t ∧
      t≤350*(n+1)^2 := by
  have h1 := GraphVerifier.Runtime.matrixLookupOn_executes (edgeEmbedding 0) g
    (state n u.val v.val w.val G.bits original outer middle inner [acc] [] [] [] [] []) n u.val w.val G.bits
    (by funext i;fin_cases i <;> rfl)
  have e1 : Function.update (state n u.val v.val w.val G.bits original outer middle inner [acc] [] [] [] [] [])
      (edgeEmbedding 0 4) (G.bits[w.val+n*u.val]?.toList)=
      state n u.val v.val w.val G.bits original outer middle inner [acc] [G.edge u w] [] [] [] [] := by
    rw [matrix_bit]
    funext i;fin_cases i <;> rfl
  rw [e1] at h1
  have h2 := GraphVerifier.Runtime.matrixLookupOn_executes (edgeEmbedding 1) g
    (state n u.val v.val w.val G.bits original outer middle inner [acc] [G.edge u w] [] [] [] []) n u.val v.val G.bits
    (by funext i;fin_cases i <;> rfl)
  have e2 : Function.update (state n u.val v.val w.val G.bits original outer middle inner [acc] [G.edge u w] [] [] [] [])
      (edgeEmbedding 1 4) (G.bits[v.val+n*u.val]?.toList)=
      state n u.val v.val w.val G.bits original outer middle inner [acc] [G.edge u w] [G.edge u v] [] [] [] := by
    rw [matrix_bit]
    funext i;fin_cases i <;> rfl
  rw [e2] at h2
  have h3 := GraphVerifier.Runtime.matrixLookupOn_executes (edgeEmbedding 2) g
    (state n u.val v.val w.val G.bits original outer middle inner [acc] [G.edge u w] [G.edge u v] [] [] []) n v.val w.val G.bits
    (by funext i;fin_cases i <;> rfl)
  have e3 : Function.update (state n u.val v.val w.val G.bits original outer middle inner [acc] [G.edge u w] [G.edge u v] [] [] [])
      (edgeEmbedding 2 4) (G.bits[w.val+n*v.val]?.toList)=
      state n u.val v.val w.val G.bits original outer middle inner [acc] [G.edge u w] [G.edge u v] [G.edge v w] [] [] := by
    rw [matrix_bit]
    funext i;fin_cases i <;> rfl
  rw [e3] at h3
  let bits : Fin 19 → Bool := fun i => if i.val=3 then acc else if i.val=10 then G.edge u w
    else if i.val=11 then G.edge u v else if i.val=12 then G.edge v w else false
  have h4 : (GraphVerifier.Runtime.decision (13 : Fin 19) [3,10,11,12] decisionValue).Executes g
      (state n u.val v.val w.val G.bits original outer middle inner [acc] [G.edge u w] [G.edge u v] [G.edge v w] [] [])
      (state n u.val v.val w.val G.bits original outer middle inner [] [] [] [] [acc && cell G u v w] []) 12 := by
    have h := GraphVerifier.Runtime.decision_executes (13 : Fin 19) [3,10,11,12]
      (by decide) (by decide) decisionValue bits g
      (state n u.val v.val w.val G.bits original outer middle inner [acc] [G.edge u w] [G.edge u v] [G.edge v w] [] [])
      (by intro i hi;fin_cases i <;> simp [state,bits] at *)
    convert h using 1
    funext i;fin_cases i <;> simp [state,bits,eraseStore,decisionValue,cell]
  have h5 : (reverseOn (13 : Fin 19) 3 (by decide)).Executes g
      (state n u.val v.val w.val G.bits original outer middle inner [] [] [] [] [acc && cell G u v w] [])
      (state n u.val v.val w.val G.bits original outer middle inner [acc && cell G u v w] [] [] [] [] []) 3 := by
    convert reverseOn_executes g (13 : Fin 19) 3 (by decide) _ using 1
    funext i;fin_cases i <;> simp [state]
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3
    (seq_executes _ _ g h4 h5))),?_⟩
  have b1 := GraphVerifier.Runtime.matrixLookupCost_in_range n u.val w.val G.bits u.isLt w.isLt
  have b2 := GraphVerifier.Runtime.matrixLookupCost_in_range n u.val v.val G.bits u.isLt v.isLt
  have b3 := GraphVerifier.Runtime.matrixLookupCost_in_range n v.val w.val G.bits v.isLt w.isLt
  nlinarith

lemma cellProgram_queryFree : cellProgram.QueryFree := seq_queryFree _ _ (GraphVerifier.Runtime.matrixLookupOn_queryFree _)
  (seq_queryFree _ _ (GraphVerifier.Runtime.matrixLookupOn_queryFree _)
    (seq_queryFree _ _ (GraphVerifier.Runtime.matrixLookupOn_queryFree _)
      (seq_queryFree _ _ (GraphVerifier.Runtime.decision_queryFree _ _ _) (reverseOn_queryFree _ _ _))))

end HiddenCircuits.GraphReduction.Runtime.UnitRecognitionUmbrella
