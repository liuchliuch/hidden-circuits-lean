import HiddenCircuits.Circuit.Runtime.DeltaWordProgram
import HiddenCircuits.Complexity.PolynomialBounds

/-! Polynomial execution time is derived from the actual
emitter and its execution storage bound, including reversal of the physical word. -/
namespace HiddenCircuits.Circuit.Runtime.DeltaWordEmitter
open HiddenCircuits.Complexity OracleBlock Polynomial SampleEmitter

def inputSize {n : ℕ} (w : List (DeltaGate n)) (r s u : ℕ) : ℕ :=
  (circuitBits n w).length+r+s+u
noncomputable def deltaBound : Polynomial ℕ := 2000000*(5*X+1)^2+ProjectionStream.time+2
noncomputable def gateBound : Polynomial ℕ := (2*X+1)*(deltaBound+2)+10*X+9
noncomputable def emitTime : Polynomial ℕ := 142*X+67+2*ProjectionStream.time+X*(gateBound+24*X+99)
noncomputable def time : Polynomial ℕ := 3*emitTime+3*X+6

lemma circuit_size_bounds {n : ℕ} (w : List (DeltaGate n)) :
    n ≤ (circuitBits n w).length ∧ w.length ≤ (circuitBits n w).length := by
  simpa [circuitBits] using SampleEmitter.circuit_size_bounds (w.map DeltaGate.descriptor)

set_option maxHeartbeats 800000 in
lemma input_store_bound {n : ℕ} (w : List (DeltaGate n)) (r s u : ℕ) :
    ∀i, (store (circuitBits n w) r s u 0 0 0 [] [] [] [] [] [] i).length ≤ inputSize w r s u := by
  intro i
  fin_cases i <;> simp [store,inputSize] <;> omega

lemma rawCost_bound {n : ℕ} (w : List (DeltaGate n)) (r s u : ℕ) :
    rawCost n (circuitBits n w).length w.length r s u ≤ emitTime.eval (inputSize w r s u) := by
  let N := inputSize w r s u
  have hn : n≤N := le_trans (circuit_size_bounds w).1 (by dsimp [N,inputSize];omega)
  have hw : w.length≤N := le_trans (circuit_size_bounds w).2 (by dsimp [N,inputSize];omega)
  have hL : (circuitBits n w).length≤N := by dsimp [N,inputSize];omega
  have hu : u≤N := by dsimp [N,inputSize];omega
  have hrs : r+s≤N := by dsimp [N,inputSize];omega
  have hp := polynomial_nat_eval_mono ProjectionStream.time hn
  dsimp only at hp
  have hd : deltaTime n u ≤ deltaBound.eval N := by
    have hpow := Nat.pow_le_pow_left (show 4*n+u+1≤5*N+1 by omega) 2
    simp only [deltaTime,deltaBound,eval_add,eval_mul,eval_pow,eval_X,eval_ofNat,eval_one]
    omega
  have hg : gateTime n r s u ≤ gateBound.eval N := by
    have hm := Nat.le_mul_of_pos_left (deltaBound.eval N+2) (show 0<2*N+1 by omega)
    simp only [gateTime,gateBound,eval_add,eval_mul,eval_X,eval_ofNat,eval_one]
    omega
  have hm := Nat.mul_le_mul hw (show gateTime n r s u+24*n+99≤gateBound.eval N+24*N+99 by omega)
  simp only [rawCost,emitTime,eval_add,eval_mul,eval_X,eval_ofNat,eval_one]
  change 5*(circuitBits n w).length+137*n+67+2*ProjectionStream.time.eval n+
    w.length*(gateTime n r s u+24*n+99) ≤ 142*N+67+2*ProjectionStream.time.eval N+N*(gateBound.eval N+24*N+99)
  omega

theorem program_executes (g : BitString → ℕ) {n : ℕ} (hn : 0<n)
    (w : List (DeltaGate n)) (r s u : ℕ) :
    ∃cost, program.Executes g (store (circuitBits n w) r s u 0 0 0 [] [] [] [] [] [])
      (outputStore (circuitBits n w) r s u 0
        (List.replicate (sampleExponent w u) true) [sampleNegative w false]
        (wordBits (compileWordInstance hn (w.map (DeltaGate.compileSample u)) (zeroBits n) (zeroBits n)))) cost ∧
      cost ≤ time.eval (inputSize w r s u) := by
  obtain ⟨a,ha,hab⟩ := emit_executes g w r s u
  have hlen := ha.stack_bound (input_store_bound w r s u) (5:Fin 32)
  change (rawBits w r s u).reverse.length ≤ inputSize w r s u+a at hlen
  rw [List.length_reverse] at hlen
  have hb := finish_executes g (circuitBits n w) r s u n (rawBits w r s u)
    (List.replicate (sampleExponent w u) true) [sampleNegative w false]
  have hh := seq_executes _ _ g ha hb
  rw [rawBits_eq_wordBits hn] at hh hlen
  refine ⟨_,hh,?_⟩
  have hraw := rawCost_bound w r s u
  have hn' : n ≤ inputSize w r s u := le_trans (circuit_size_bounds w).1 (by unfold inputSize;omega)
  simp only [time,eval_add,eval_mul,eval_ofNat,eval_X]
  omega

/-- Both physically emitted objects have polynomial byte size, independently of
any evaluation result or oracle response. -/
theorem emitted_length_bound (g : BitString → ℕ) {n : ℕ} (w : List (DeltaGate n)) (r s u : ℕ) :
    (rawBits w r s u).length ≤ inputSize w r s u+emitTime.eval (inputSize w r s u) ∧
    sampleExponent w u ≤ inputSize w r s u+emitTime.eval (inputSize w r s u) := by
  obtain ⟨a,ha,hab⟩ := emit_executes g w r s u
  have h5 := ha.stack_bound (input_store_bound w r s u) (5:Fin 32)
  have h6 := ha.stack_bound (input_store_bound w r s u) (6:Fin 32)
  change (rawBits w r s u).reverse.length ≤ inputSize w r s u+a at h5
  change (List.replicate (sampleExponent w u) true).length ≤ inputSize w r s u+a at h6
  simp only [List.length_reverse,List.length_replicate] at h5 h6
  have hraw := rawCost_bound w r s u
  omega

noncomputable def on {k : ℕ} (φ : Fin 32 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 32 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    {n : ℕ} (hn : 0<n) (w : List (DeltaGate n)) (r t u : ℕ)
    (hs : s∘φ=store (circuitBits n w) r t u 0 0 0 [] [] [] [] [] []) :
    ∃cost, (on φ).Executes g s
      (Function.update (Function.update (Function.update s (φ 6)
        (List.replicate (sampleExponent w u) true)) (φ 7) [sampleNegative w false])
        (φ 31) (wordBits (compileWordInstance hn (w.map (DeltaGate.compileSample u)) (zeroBits n) (zeroBits n)))) cost ∧
      cost ≤ time.eval (inputSize w r t u) := by
  obtain ⟨c,hc,hb⟩ := program_executes g hn w r t u
  refine ⟨c,?_,hb⟩
  apply rename_executes_to program φ g hc hs
  · funext i
    have hi := congrFun hs i
    change s (φ i)=_ at hi
    simp only [Function.comp_def,Function.update_apply,φ.injective.eq_iff,hi]
    fin_cases i <;> rfl
  · intro i hi
    simp only [Function.update_of_ne (hi 6).symm,Function.update_of_ne (hi 7).symm,Function.update_of_ne (hi 31).symm]
lemma on_queryFree {k : ℕ} (φ : Fin 32 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ program_queryFree
end HiddenCircuits.Circuit.Runtime.DeltaWordEmitter
