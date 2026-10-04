import HiddenCircuits.Circuit.Runtime.SourceScanLoop
import HiddenCircuits.Circuit.Runtime.UniformGateCorrectness
import HiddenCircuits.Complexity.CNFEmitter
import HiddenCircuits.Complexity.BinaryArithmetic.AccumulatorProduct

/-! Canonical graph parsing, circuit header emission, and primitive uniform stages. -/
namespace HiddenCircuits.Circuit.Runtime.SourceCircuitEmitter
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

/-- Source-grid masters0/1, true wire count9, matrix payload10, reversed circuit
stream11, normalization clock12, and transient parser flag15. -/
def store (a b n : ℕ) (payload output : BitString) (swaps : ℕ) (flag : BitString := []) : Store 35 := fun q =>
  if q.val=0 then List.replicate a true else if q.val=1 then List.replicate b true else
  if q.val=9 then List.replicate n true else if q.val=10 then payload else if q.val=11 then output else
  if q.val=12 then List.replicate swaps true else if q.val=15 then flag else []

def parseEmbedding : Fin 4 ↪ Fin 36 where
  toFun q := if q.val=0 then 10 else if q.val=1 then 9 else if q.val=2 then 16 else 15
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

def uniformEmbedding : Fin 6 ↪ Fin 36 where
  toFun q := if q.val=0 then 9 else if q.val=1 then 16 else if q.val=2 then 17 else
    if q.val=3 then 11 else if q.val=4 then 18 else 19
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

noncomputable def parseGraph : OracleBlock 35 := seq (moveOn 0 10 16 (by decide) (by decide) (by decide))
  (seq (GraphVerifier.Runtime.unpairOn parseEmbedding) (clear 15))

theorem parseGraph_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixGraph n) :
    parseGraph.Executes g (Function.update (fun _ => []) 0 (GraphInput.encode ⟨n,G⟩))
      (store 0 0 n G.bits [] 0) (6*(GraphInput.encode ⟨n,G⟩).length+5*n+14) := by
  let bits := GraphInput.encode ⟨n,G⟩
  have h₀ : (moveOn (0 : Fin 36) 10 16 (by decide) (by decide) (by decide)).Executes g
      (Function.update (fun _ => []) 0 bits) (store 0 0 0 bits [] 0) (6*bits.length+5) := by
    convert moveOn_executes g (0 : Fin 36) 10 16 (by decide) (by decide) (by decide)
      (Function.update (fun _ => []) 0 bits) rfl using 1
    funext q;fin_cases q <;> simp [store]
  have h₁ : (GraphVerifier.Runtime.unpairOn parseEmbedding).Executes g
      (store 0 0 0 bits [] 0) (store 0 0 n G.bits [] 0 [true]) (5*n+3) := by
    have h := GraphVerifier.Runtime.unpairOn_executes parseEmbedding g
      (store 0 0 0 bits [] 0) (store 0 0 n G.bits [] 0 [true]) bits
      (by funext q;fin_cases q <;> rfl)
      (by funext q;fin_cases q <;> simp only [bits,GraphInput.encode,GraphVerifier.parse_pair] <;> rfl)
      (by intro q hq;fin_cases q <;> first | rfl | (exfalso;exact hq 0 rfl) | (exfalso;exact hq 1 rfl) | (exfalso;exact hq 3 rfl))
    convert h using 1
    simp [bits,GraphInput.encode,GraphVerifier.parse_pair,BinaryArithmetic.pair_parse_cost]
    omega
  have h₂ : (clear (15 : Fin 36)).Executes g (store 0 0 n G.bits [] 0 [true]) (store 0 0 n G.bits [] 0) 2 := by
    convert clear_executes g (15 : Fin 36) (store 0 0 n G.bits [] 0 [true]) using 1
    funext q;fin_cases q <;> rfl
  convert seq_executes _ _ g h₀ (seq_executes _ _ g h₁ h₂) using 1 <;> simp only [bits] <;> omega

def headerBits (n : ℕ) : BitString := List.replicate (2*n) true++[false]
noncomputable def header : OracleBlock 35 := seq (copyOn 9 16 18 (by decide) (by decide) (by decide)) (CNFEmitter.header 16 11)

lemma header_executes (g : BitString → ℕ) (a b n : ℕ) (payload out : BitString) (swaps : ℕ) :
    header.Executes g (store a b n payload out swaps)
      (store a b n payload ((headerBits n).reverse++out) swaps) (14*n+8) := by
  let middle := Function.update (store a b n payload out swaps) (16 : Fin 36) (List.replicate n true)
  have h₀ : (copyOn (9 : Fin 36) 16 18 (by decide) (by decide) (by decide)).Executes g
      (store a b n payload out swaps) middle (5*n+2) := by
    convert copyOn_executes g (9 : Fin 36) 16 18 (by decide) (by decide) (by decide)
      (store a b n payload out swaps) rfl using 1
    · funext q;fin_cases q <;> simp [middle,store]
    · simp [store]
  have h₁ : (CNFEmitter.header (16 : Fin 36) 11).Executes g middle
      (store a b n payload ((headerBits n).reverse++out) swaps) (9*n+4) := by
    convert CNFEmitter.header_executes g (16 : Fin 36) 11 (by decide) middle using 1
    · funext q;fin_cases q <;> simp [middle,store,headerBits,List.reverse_append,List.append_assoc]
    · simp [middle]
  convert seq_executes _ _ g h₀ h₁ using 1 <;> omega

noncomputable def uniform (one : OneGate) : OracleBlock 35 := rename (UniformGateEmitter.program (tagOfOne one)) uniformEmbedding

lemma uniform_executes (g : BitString → ℕ) (one : OneGate) (a b n : ℕ) (payload out : BitString) (swaps : ℕ) :
    ∃ c, (uniform one).Executes g (store a b n payload out swaps)
      (store a b n payload ((SourceScan.gateStream (uniformOneProgram one n).gates).reverse++out) swaps) c ∧
      c≤14*n^2+79*n+8 := by
  obtain ⟨c,hc,hb⟩ := uniformGate_executes g one n out
  refine ⟨c,?_,hb⟩
  apply rename_executes_to _ uniformEmbedding g hc
  · funext q;fin_cases q <;> rfl
  · funext q;fin_cases q <;> rfl
  · intro q hq;fin_cases q <;> first | rfl | (exfalso;exact hq 3 rfl)

lemma parseGraph_queryFree : parseGraph.QueryFree := seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (GraphVerifier.Runtime.unpairOn_queryFree _) (clear_queryFree _))
lemma header_queryFree : header.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (CNFEmitter.header_queryFree _ _)
lemma uniform_queryFree (one : OneGate) : (uniform one).QueryFree := rename_queryFree _ _ (UniformGateEmitter.program_queryFree _)

end HiddenCircuits.Circuit.Runtime.SourceCircuitEmitter
