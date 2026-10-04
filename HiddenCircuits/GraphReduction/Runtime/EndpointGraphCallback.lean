import HiddenCircuits.GraphReduction.Runtime.EndpointGraphCallbackStages
namespace HiddenCircuits.GraphReduction.Runtime.EndpointGraph
open Complexity OracleBlock Approximation MonotoneEndpointEncoding
set_option maxHeartbeats 1500000
set_option maxRecDepth 3000

def flagPorts : List (Fin 32) := [13,14,19,20,21,22]
def cleanupPorts : List (Fin 32) := [11,12,15,16,17,18]
def afterGate {n : ℕ} (E : MonotoneEndpoints n) (i j : ℕ) (out inner outer : BitString) : Store 31 :=
  Function.update (eraseStore flagPorts (stage E i j 10 out inner outer)) 3 [edge n (endpoint E.lo) (endpoint E.hi) i j]
lemma decideEdge_executes {n : ℕ} (g : BitString → ℕ) (E : MonotoneEndpoints n) (i j : ℕ)
    (out inner outer : BitString) :
    decideEdge.Executes g (stage E i j 10 out inner outer) (afterGate E i j out inner outer) 16 := by
  let b : Fin 32 → Bool := fun q => if q.val=13 then flags E i j 0 else if q.val=14 then flags E i j 1
    else if q.val=19 then flags E i j 2 else if q.val=20 then flags E i j 3 else if q.val=21 then flags E i j 4 else flags E i j 5
  have hh := GraphVerifier.Runtime.decision_executes (3:Fin 32) flagPorts (by decide) (by decide)
    gate b g (stage E i j 10 out inner outer) (by
      intro q hq
      simp only [flagPorts,List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl)
  have he : gate (flagPorts.map b)=edge n (endpoint E.lo) (endpoint E.hi) i j := rfl
  rw [he] at hh
  exact hh

lemma cleanup_executes {n : ℕ} (g : BitString → ℕ) (E : MonotoneEndpoints n) (i j : ℕ)
    (out inner outer : BitString) (hi:i<2*n) (hj:j<2*n) :
    ∃c, (clearList cleanupPorts).Executes g (afterGate E i j out inner outer)
      (callbackState E i j [edge n (endpoint E.lo) (endpoint E.hi) i j] out inner outer) c ∧ c ≤ 6*(2*n+3)+1 := by
  have h0 := value_bound E i j 0
  have h1 := value_bound E i j 1
  have h2 := value_bound E i j 2
  have h3 := value_bound E i j 3
  have hs : ∀q∈cleanupPorts,(afterGate E i j out inner outer q).length ≤ 2*n := by
    intro q hq
    simp only [cleanupPorts,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [afterGate,eraseStore,flagPorts,stage,callbackState,MatrixEmitter.store,MatrixEmitter.port,params] <;> omega
  obtain ⟨c,hc,hcb⟩ := clearList_executes_local g cleanupPorts (afterGate E i j out inner outer) (2*n) hs
  have he : eraseStore cleanupPorts (afterGate E i j out inner outer)=
      callbackState E i j [edge n (endpoint E.lo) (endpoint E.hi) i j] out inner outer := by
    funext q;fin_cases q <;> simp [afterGate,eraseStore,flagPorts,cleanupPorts,stage,callbackState,MatrixEmitter.store,MatrixEmitter.port,params]
  rw [he] at hc
  exact ⟨c,hc,hcb⟩

theorem callback_executes {n : ℕ} (g : BitString → ℕ) (E : MonotoneEndpoints n) (i j : ℕ)
    (out inner outer : BitString) (hi:i<2*n) (hj:j<2*n) :
    ∃c, callback.Executes g (callbackState E i j [] out inner outer)
      (callbackState E i j [edge n (endpoint E.lo) (endpoint E.hi) i j] out inner outer) c ∧
      c ≤ callbackBound n (dataLength E) := by
  obtain ⟨a,ha,hab⟩ := splitIndex_executes g E false i j out inner outer
  obtain ⟨b,hb,hbb⟩ := splitIndex_executes g E true i j out inner outer
  obtain ⟨c,hc,hcb⟩ := lookup_executes g E 0 i j out inner outer hi hj
  obtain ⟨d,hd,hdb⟩ := lookup_executes g E 1 i j out inner outer hi hj
  obtain ⟨e,he,heb⟩ := lookup_executes g E 2 i j out inner outer hi hj
  obtain ⟨f,hf,hfb⟩ := lookup_executes g E 3 i j out inner outer hi hj
  obtain ⟨h,hh,hhb⟩ := compare_executes g E 0 i j out inner outer hi hj
  obtain ⟨k,hk,hkb⟩ := compare_executes g E 1 i j out inner outer hi hj
  obtain ⟨l,hl,hlb⟩ := compare_executes g E 2 i j out inner outer hi hj
  obtain ⟨m,hm,hmb⟩ := compare_executes g E 3 i j out inner outer hi hj
  have hgate := decideEdge_executes g E i j out inner outer
  obtain ⟨z,hz,hzb⟩ := cleanup_executes g E i j out inner outer hi hj
  change (splitIndex false).Executes g (stage E i j 0 out inner outer) (stage E i j 1 out inner outer) a at ha
  rw [stage_zero] at ha
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb (seq_executes _ _ g hc
    (seq_executes _ _ g hd (seq_executes _ _ g he (seq_executes _ _ g hf
      (seq_executes _ _ g hh (seq_executes _ _ g hk (seq_executes _ _ g hl
        (seq_executes _ _ g hm (seq_executes _ _ g hgate hz)))))))))),?_⟩
  change a ≤ 5*i+14*n+12 at hab
  change b ≤ 5*j+14*n+12 at hbb
  unfold callbackBound
  omega

lemma splitIndex_queryFree (second : Bool) : (splitIndex second).QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (CNFCloneEmitter.UnarySplit.on_queryFree _))
lemma callback_queryFree : callback.QueryFree := seq_queryFree _ _ (splitIndex_queryFree false) (seq_queryFree _ _ (splitIndex_queryFree true) (seq_queryFree _ _ (listLookupOn_queryFree (lookupMap 0)) (seq_queryFree _ _ (listLookupOn_queryFree (lookupMap 1)) (seq_queryFree _ _ (listLookupOn_queryFree (lookupMap 2)) (seq_queryFree _ _ (listLookupOn_queryFree (lookupMap 3)) (seq_queryFree _ _ (readOnlyLTOn_queryFree (compareMap 0)) (seq_queryFree _ _ (readOnlyLTOn_queryFree (compareMap 1)) (seq_queryFree _ _ (readOnlyLTOn_queryFree (compareMap 2)) (seq_queryFree _ _ (readOnlyLTOn_queryFree (compareMap 3)) (seq_queryFree _ _ (GraphVerifier.Runtime.decision_queryFree _ _ _) (clearList_queryFree _)))))))))))
end HiddenCircuits.GraphReduction.Runtime.EndpointGraph
