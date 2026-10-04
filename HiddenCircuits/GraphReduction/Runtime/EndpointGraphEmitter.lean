import HiddenCircuits.GraphReduction.Runtime.EndpointGraphCallback
import HiddenCircuits.Approximation.SamplerRuntime.EndpointParserProgram
import HiddenCircuits.Complexity.OracleResult
import HiddenCircuits.Complexity.OracleMove

namespace HiddenCircuits.GraphReduction.Runtime.EndpointGraph
open Complexity OracleBlock Approximation MonotoneEndpointEncoding Polynomial
set_option maxHeartbeats 1500000

def preState (xs : BitString) {n : ℕ} (E : MonotoneEndpoints n) : Store 39 := fun q =>
  if q.val=0 then xs else if q.val=1 then List.replicate n true else if q.val=2 then encodeBitList (rows E.lo)
  else if q.val=3 then encodeBitList (rows E.hi) else []
def ready {n : ℕ} (E : MonotoneEndpoints n) : Store 39 := fun q =>
  if q.val=0 then List.replicate (2*n) true else if q.val=8 then List.replicate n true
  else if q.val=9 then encodeBitList (rows E.lo) else if q.val=10 then encodeBitList (rows E.hi) else []
def emitterMap : Fin 32 ↪ Fin 40 := Fin.castAddEmb 8
noncomputable def emit : OracleBlock 39 := rename (MatrixEmitter.block callback) emitterMap
noncomputable def prepare : OracleBlock 39 := seq (moveOn 2 9 27 (by decide) (by decide) (by decide))
  (seq (moveOn 3 10 27 (by decide) (by decide) (by decide))
    (seq (moveOn 1 8 27 (by decide) (by decide) (by decide)) (seq (clear 0)
      (seq (copyOn 8 0 27 (by decide) (by decide) (by decide)) (copyOn 8 0 27 (by decide) (by decide) (by decide)))) ))

lemma prepare_executes {n : ℕ} (g : BitString → ℕ) (xs : BitString) (E : MonotoneEndpoints n) :
    prepare.Executes g (preState xs E) (ready E)
      (xs.length+16*n+6*(encodeBitList (rows E.lo)).length+6*(encodeBitList (rows E.hi)).length+30) := by
  let s0 := preState xs E
  let s1 := Function.update (Function.update s0 (9:Fin 40) (s0 2++s0 9)) 2 []
  let s2 := Function.update (Function.update s1 (10:Fin 40) (s1 3++s1 10)) 3 []
  let s3 := Function.update (Function.update s2 (8:Fin 40) (s2 1++s2 8)) 1 []
  let s4 := Function.update s3 (0:Fin 40) []
  let s5 := Function.update s4 (0:Fin 40) (s4 8++s4 0)
  let s6 := Function.update s5 (0:Fin 40) (s5 8++s5 0)
  have h1 := moveOn_executes g (2:Fin 40) 9 27 (by decide) (by decide) (by decide) s0 rfl
  have h2 := moveOn_executes g (3:Fin 40) 10 27 (by decide) (by decide) (by decide) s1 rfl
  have h3 := moveOn_executes g (1:Fin 40) 8 27 (by decide) (by decide) (by decide) s2 rfl
  have h4 := clear_executes g (0:Fin 40) s3
  have h5 := copyOn_executes g (8:Fin 40) 0 27 (by decide) (by decide) (by decide) s4 rfl
  have h6 := copyOn_executes g (8:Fin 40) 0 27 (by decide) (by decide) (by decide) s5 rfl
  have hh := seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3
    (seq_executes _ _ g h4 (seq_executes _ _ g h5 h6))))
  have he : s6=ready E := by
    funext q;fin_cases q <;> simp [s6,s5,s4,s3,s2,s1,s0,preState,ready,←List.replicate_add,two_mul]
  change prepare.Executes g s0 s6 _ at hh
  rw [he] at hh
  convert hh using 1
  simp [s5,s4,s3,s2,s1,s0,preState]
  omega

lemma queryBits_eq {n : ℕ} (E : MonotoneEndpoints n) :
    MatrixEmitter.queryBits (2*n) (edge n (endpoint E.lo) (endpoint E.hi))=(graph ⟨n,E⟩).encode := by
  rw [Nat.two_mul]
  exact MatrixEmitter.queryBits_graph (matrix E) _ (by intros;rfl)

lemma emit_executes {n : ℕ} (g : BitString → ℕ) (E : MonotoneEndpoints n) :
    ∃c, emit.Executes g (ready E) (Function.update (ready E) 7 (graph ⟨n,E⟩).encode) c ∧
      c ≤ (2*n)*(2*n)*(callbackBound n (dataLength E)+18)+80*n+30 := by
  obtain ⟨c,hc,hcb⟩ := MatrixEmitter.block_executes callback (edge n (endpoint E.lo) (endpoint E.hi)) (2*n)
    (callbackBound n (dataLength E)) (params E)
    (fun g i j out inner outer hi hj => callback_executes g E i j out inner outer hi hj) g
  rw [queryBits_eq] at hc
  refine ⟨c,?_,by omega⟩
  apply rename_executes_to (MatrixEmitter.block callback) emitterMap g hc
  · funext q;fin_cases q <;> rfl
  · funext q;fin_cases q <;> rfl
  · intro q hq
    have h7 : q≠(7:Fin 40) := fun h=>hq 7 h.symm
    exact Function.update_of_ne h7 _ _

lemma data_length_of_decode {xs : BitString} {E : Input} (h : decode xs=some E) :
    (encodeBitList (rows E.2.lo)).length ≤ xs.length ∧ (encodeBitList (rows E.2.hi)).length ≤ xs.length := by
  have hf := SamplerRuntime.EndpointParser.fields_of_decode h
  have hb := SamplerRuntime.EndpointParser.fields_lengths xs
  rw [hf.2.1] at hb
  rw [hf.2.2] at hb
  exact hb.2
lemma callback_bound {n : ℕ} (E : MonotoneEndpoints n) (L : ℕ) (hn:n ≤ L) (hL:dataLength E ≤ 2*L) :
    callbackBound n (dataLength E) ≤ 1000*(L+1)^2 := by
  calc
    _ ≤ callbackBound L (2*L) := by unfold callbackBound lookupBound;gcongr
    _ ≤ _ := by unfold callbackBound lookupBound;ring_nf;omega

lemma emit_polynomial {xs : BitString} {E : Input} (h : decode xs=some E) (g : BitString → ℕ) :
    ∃c, emit.Executes g (ready E.2) (Function.update (ready E.2) 7 (graph E).encode) c ∧
      c ≤ 5000*(xs.length+1)^4 := by
  obtain ⟨c,hc,hcb⟩ := emit_executes g E.2
  refine ⟨c,hc,hcb.trans ?_⟩
  have hn := MonotoneEndpointEncoding.size_le_of_decode h
  have hd := data_length_of_decode h
  have ht := callback_bound E.2 xs.length hn (by unfold dataLength;omega)
  calc
    _ ≤ (2*xs.length)*(2*xs.length)*(1000*(xs.length+1)^2+18)+80*xs.length+30 := by gcongr
    _ ≤ _ := by ring_nf;omega

lemma prepare_queryFree : prepare.QueryFree := seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (copyOn_queryFree _ _ _ _ _ _)))))
lemma emit_queryFree : emit.QueryFree := rename_queryFree _ _ (MatrixEmitter.block_queryFree _ callback_queryFree)
end HiddenCircuits.GraphReduction.Runtime.EndpointGraph
