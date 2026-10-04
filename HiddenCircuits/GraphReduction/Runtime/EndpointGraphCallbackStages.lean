import HiddenCircuits.GraphReduction.Runtime.EndpointGraphCallbackDefs
namespace HiddenCircuits.GraphReduction.Runtime.EndpointGraph
open Complexity OracleBlock Approximation MonotoneEndpointEncoding CNFCloneEmitter
set_option maxHeartbeats 1500000

lemma splitIndex_executes {n : ℕ} (g : BitString → ℕ) (E : MonotoneEndpoints n) (second : Bool)
    (i j : ℕ) (out inner outer : BitString) :
    ∃c, (splitIndex second).Executes g (stage E i j (if second then 1 else 0) out inner outer)
      (stage E i j (if second then 2 else 1) out inner outer) c ∧
      c ≤ 5*(if second then j else i)+14*n+12 := by
  let src : Fin 32 := if second then 2 else 1
  let dest : Fin 32 := if second then 12 else 11
  let st := stage E i j (if second then 1 else 0) out inner outer
  let a := Function.update st dest (List.replicate (if second then j else i) true)
  let b := Function.update a (26:Fin 32) (List.replicate n true)
  have h1 : (copyOn src dest 27 (by cases second <;> decide) (by cases second <;> decide)
      (by cases second <;> decide)).Executes g st a (5*(if second then j else i)+2) := by
    cases second <;> simpa [src,dest,st,a,stage,callbackState,MatrixEmitter.store,MatrixEmitter.port,params] using
      copyOn_executes g src dest 27 (by simp [src,dest]) (by simp [src]) (by simp [dest]) st rfl
  have h2 : (copyOn (8:Fin 32) 26 27 (by decide) (by decide) (by decide)).Executes g a b (5*n+2) := by
    cases second <;> simpa [src,dest,st,a,b,stage,callbackState,MatrixEmitter.store,MatrixEmitter.port,params] using
      copyOn_executes g (8:Fin 32) 26 27 (by decide) (by decide) (by decide) a rfl
  obtain ⟨c,hc,hcb⟩ := UnarySplit.on_executes (splitMap second) g b (if second then j else i) n
    (by cases second <;> funext q <;> fin_cases q <;> rfl)
  have h3 : (UnarySplit.on (splitMap second)).Executes g b (stage E i j (if second then 2 else 1) out inner outer) c := by
    convert hc using 1
    funext q;cases second <;> fin_cases q <;>
      simp [b,a,st,src,dest,splitMap,stage,flags,callbackState,MatrixEmitter.store,MatrixEmitter.port,params]
  exact ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 h3),by omega⟩

lemma lookup_executes {n : ℕ} (g : BitString → ℕ) (E : MonotoneEndpoints n) (r : Fin 4)
    (i j : ℕ) (out inner outer : BitString) (hi:i<2*n) (hj:j<2*n) :
    ∃c, (lookup r).Executes g (stage E i j (r.val+2) out inner outer)
      (stage E i j (r.val+3) out inner outer) c ∧ c ≤ lookupBound (dataLength E) (2*n) := by
  let f := if r.val=0 ∨ r.val=2 then E.lo else E.hi
  let v := if r.val<2 then i else j
  let st := stage E i j (r.val+2) out inner outer
  obtain ⟨c,hc,hcb⟩ := listLookupOn_executes (lookupMap r) g st (rows f) v
    (by fin_cases r <;> funext q <;> fin_cases q <;> rfl)
  rw [row_lookup] at hc
  refine ⟨c,?_,hcb.trans ?_⟩
  · convert hc using 1
    funext q;fin_cases r <;> fin_cases q <;> simp [st,f,v,lookupMap,stage,value]
  · have hlen : (encodeBitList (rows f)).length ≤ dataLength E := by
      dsimp [f,dataLength];split_ifs <;> omega
    have hv : v ≤ 2*n := by dsimp [v];split_ifs <;> omega
    unfold lookupBound
    gcongr

lemma compare_executes {n : ℕ} (g : BitString → ℕ) (E : MonotoneEndpoints n) (r : Fin 4)
    (i j : ℕ) (out inner outer : BitString) (hi:i<2*n) (hj:j<2*n) :
    ∃c, (compare r).Executes g (stage E i j (r.val+6) out inner outer)
      (stage E i j (r.val+7) out inner outer) c ∧ c ≤ 26*n+15 := by
  let x := if r.val<2 then j-n else i-n
  let st := stage E i j (r.val+6) out inner outer
  obtain ⟨c,hc,hcb⟩ := readOnlyLTOn_executes (compareMap r) g st x (value E i j r)
    (by fin_cases r <;> funext q <;> fin_cases q <;> rfl)
  refine ⟨c,?_,?_⟩
  · convert hc using 1
    funext q;fin_cases r <;> fin_cases q <;> simp [st,x,compareMap,stage,value,flags]
  · have hx : x ≤ 2*n := by dsimp [x];split_ifs <;> omega
    have hy := value_bound E i j r
    omega
end HiddenCircuits.GraphReduction.Runtime.EndpointGraph
