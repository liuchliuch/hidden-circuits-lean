import HiddenCircuits.GraphReduction.Runtime.PrivateIntervalOrderTranspose
import HiddenCircuits.GraphReduction.Runtime.CliqueCallback

/-! A physical endpoint-count predicate, short-circuiting a transposed structural
order scan with the actual private-graph nonadjacency predicate. -/
namespace HiddenCircuits.GraphReduction.Runtime.PrivateIntervalCallback
open Complexity OracleBlock
set_option maxHeartbeats 900000

noncomputable def graph : OracleBlock 56 := rename (CliqueCallback.program true) PrivateIntervalOrderTranspose.embedding
noncomputable def negate : OracleBlock 56 := branchPop 3 (push 3 true) (push 3 true) (push 3 false)
noncomputable def tail (left : Bool) : OracleBlock 56 :=
  branchPop 3 (push 3 false) (push 3 false) (if left then seq graph negate else push 3 true)
noncomputable def program (left : Bool) : OracleBlock 56 := seq (PrivateIntervalOrderTranspose.program false) (tail left)
def bound (n L : ℕ) := PrivateIntervalOrderRuntime.bound n L+CliqueCallback.bound n L+10

lemma update_bit (n i j : ℕ) (old bit out inner outer : BitString) (params : Store 56) :
    Function.update (MatrixEmitter.store (k:=49) n i j old out inner outer params) (3:Fin 57) bit=
      MatrixEmitter.store (k:=49) n i j bit out inner outer params := by
  funext q;fin_cases q <;> rfl

lemma push_bit (g : BitString→ℕ) (n i j : ℕ) (b : Bool) (out inner outer : BitString) (params : Store 56) :
    (push (3:Fin 57) b).Executes g (MatrixEmitter.store (k:=49) n i j [] out inner outer params)
      (MatrixEmitter.store (k:=49) n i j [b] out inner outer params) 1 := by
  have h:=push_executes g (3:Fin 57) b (MatrixEmitter.store (k:=49) n i j [] out inner outer params)
  simpa only [show MatrixEmitter.store (k:=49) n i j [] out inner outer params 3=[] by rfl,update_bit] using h

lemma negate_executes (g : BitString→ℕ) (n i j : ℕ) (b : Bool) (out inner outer : BitString) (params : Store 56) :
    negate.Executes g (MatrixEmitter.store (k:=49) n i j [b] out inner outer params)
      (MatrixEmitter.store (k:=49) n i j [!b] out inner outer params) 3 := by
  have h:=push_bit g n i j (!b) out inner outer params
  cases b
  · apply branchPop_false _ _ _ _ g (by rfl)
    rwa [update_bit]
  · apply branchPop_true _ _ _ _ g (by rfl)
    rwa [update_bit]

lemma graph_framed (g : BitString→ℕ) (records : List VertexRecord) (i j : ℕ)
    (hi:i<records.length) (hj:j<records.length) (out inner outer : BitString) :
    ∃t,graph.Executes g
      (MatrixEmitter.store (k:=49) records.length i j [] out inner outer (callbackParams (encodeBitList (records.map encodeVertex))))
      (MatrixEmitter.store (k:=49) records.length i j [CliqueCallback.recordEdge true records j i] out inner outer (callbackParams (encodeBitList (records.map encodeVertex)))) t ∧
      t≤CliqueCallback.bound records.length (encodeBitList (records.map encodeVertex)).length := by
  obtain ⟨t,hc,hb⟩:=CliqueCallback.framed g true records j i hj hi out inner outer
  refine ⟨t,?_,hb⟩
  apply rename_executes_to (CliqueCallback.program true) PrivateIntervalOrderTranspose.embedding g hc
  · funext q;fin_cases q <;> rfl
  · funext q;fin_cases q <;> rfl
  · intro q hq;exact False.elim (hq (PrivateIntervalOrderTranspose.embedding q) (PrivateIntervalOrderTranspose.embedding_involutive q))

lemma tail_framed (g : BitString→ℕ) (left o : Bool) (records : List VertexRecord) (i j : ℕ)
    (hi:i<records.length) (hj:j<records.length) (out inner outer : BitString) :
    ∃t,(tail left).Executes g
      (MatrixEmitter.store (k:=49) records.length i j [o] out inner outer (callbackParams (encodeBitList (records.map encodeVertex))))
      (MatrixEmitter.store (k:=49) records.length i j [o && (if left then !(CliqueCallback.recordEdge true records j i) else true)] out inner outer (callbackParams (encodeBitList (records.map encodeVertex)))) t ∧
      t≤CliqueCallback.bound records.length (encodeBitList (records.map encodeVertex)).length+7 := by
  cases o
  · refine ⟨3,?_,by omega⟩
    apply branchPop_false _ _ _ _ g (by rfl)
    rw [update_bit]
    exact push_bit g _ _ _ false _ _ _ _
  · cases left
    · refine ⟨3,?_,by omega⟩
      apply branchPop_true _ _ _ _ g (by rfl)
      rw [update_bit]
      exact push_bit g _ _ _ true _ _ _ _
    · obtain ⟨c,hc,hb⟩:=graph_framed g records i j hi hj out inner outer
      refine ⟨c+7,?_,by omega⟩
      have hn:=negate_executes g records.length i j (CliqueCallback.recordEdge true records j i) out inner outer (callbackParams (encodeBitList (records.map encodeVertex)))
      have he:=seq_executes _ _ g hc hn
      have ht:=branchPop_true (3:Fin 57) (push 3 false) (push 3 false) (seq graph negate) g
        (show MatrixEmitter.store (k:=49) records.length i j [true] out inner outer (callbackParams (encodeBitList (records.map encodeVertex))) 3=true::[] by rfl)
        (by rw [update_bit];exact he)
      simpa only [tail,Bool.true_and,ite_true,Nat.add_assoc] using ht

 theorem framed (g : BitString→ℕ) (left : Bool) (records : List VertexRecord) (i j : ℕ)
    (hi:i<records.length) (hj:j<records.length) (out inner outer : BitString) :
    ∃t,(program left).Executes g
      (MatrixEmitter.store (k:=49) records.length i j [] out inner outer (callbackParams (encodeBitList (records.map encodeVertex))))
      (MatrixEmitter.store (k:=49) records.length i j [PrivateInterval.endpointEdge left records i j] out inner outer (callbackParams (encodeBitList (records.map encodeVertex)))) t ∧
      t≤bound records.length (encodeBitList (records.map encodeVertex)).length := by
  obtain ⟨a,ha,hab⟩:=PrivateIntervalOrderTranspose.framed g false records i j hi hj out inner outer
  obtain ⟨b,hb,hbb⟩:=tail_framed g left (PrivateIntervalOrderRuntime.recordLT false records j i) records i j hi hj out inner outer
  exact ⟨_,seq_executes _ _ g ha hb,by unfold bound;omega⟩
lemma negate_queryFree : negate.QueryFree := branchPop_queryFree _ _ _ _ (push_queryFree _ _) (push_queryFree _ _) (push_queryFree _ _)
lemma program_queryFree (left : Bool) : (program left).QueryFree := by
  apply seq_queryFree _ _ (PrivateIntervalOrderTranspose.program_queryFree false)
  apply branchPop_queryFree _ _ _ _ (push_queryFree _ _) (push_queryFree _ _)
  cases left
  · exact push_queryFree _ _
  · exact seq_queryFree _ _ (rename_queryFree _ _ (CliqueCallback.program_queryFree true)) negate_queryFree
end HiddenCircuits.GraphReduction.Runtime.PrivateIntervalCallback
