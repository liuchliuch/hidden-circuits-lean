import HiddenCircuits.Circuit.Runtime.SourceReductionFrame
import HiddenCircuits.Complexity.PairSerialization

/-! Generic constraint-circuit evaluation at the zero boundary, independent of
source-graph construction. The output is an explicit nonzero-denominator signed
ratio, physically serialized by the program, with its rational value specified. -/
namespace HiddenCircuits.Circuit.Runtime.ConstraintZero
open Complexity OracleBlock BinaryArithmetic Polynomial

def metadataMap : Fin 9 ↪ Fin 64 where
  toFun i:=![0,23,5,6,24,25,26,27,28] i
  inj':=by decide +kernel
noncomputable def metadata : OracleBlock 63 := CircuitMetadata.on metadataMap
noncomputable def core {k : ℕ} (W : OracleBlock k) : OracleBlock (k+69) :=
  seq (SourceReduction.lift k metadata) (seq (SourceReduction.front k) (SourceOuter.program W))
def pairMap (k : ℕ) : Fin 3 ↪ Fin (k+70) :=
  ⟨fun i=>⟨(![12,11,24] i:ℕ),by fin_cases i <;> simp <;> omega⟩,
    by intro i j h;fin_cases i <;> fin_cases j <;> simp_all⟩
noncomputable def pair (k : ℕ) : OracleBlock (k+69) := PairSerialization.on (pairMap k)
noncomputable def packed {k : ℕ} (W : OracleBlock k) : OracleBlock (k+69) := seq (core W) (pair k)
noncomputable def cleanup (k : ℕ) : OracleBlock (k+69) := cleanResult (SourceReduction.lowPort k 12)
  (SourceReduction.lowPort k 24) (by intro h;have hh:=congrArg Fin.val h;change 12=24 at hh;omega)
  (by intro h;have hh:=congrArg Fin.val h;change 24=0 at hh;omega)
noncomputable def program {k : ℕ} (W : OracleBlock k) : OracleBlock (k+69) := seq (packed W) (cleanup k)
noncomputable def result {n : ℕ} (hn : 0<n) (w : List (ConstraintGate n)) : RationalAccumulator.Ratio :=
  SourceOuter.result hn 0 w (0,1)
def ratioBits (z : RationalAccumulator.Ratio) : BitString := pairBits (signedBits z.1) (signedBits z.2)
noncomputable def inputBound : Polynomial ℕ := X+CircuitMetadata.time
noncomputable def outerBound : Polynomial ℕ := X+SourceQueryEnumeration.prefixBitSize
noncomputable def prefixTime (p : Polynomial ℕ) : Polynomial ℕ :=
  CircuitMetadata.time+SourceReduction.frontTime.comp inputBound+(SourceOuter.time p).comp outerBound+4
noncomputable def packedTime (p : Polynomial ℕ) : Polynomial ℕ := prefixTime p+10*(X+prefixTime p)+11
noncomputable def time (k : ℕ) (p : Polynomial ℕ) : Polynomial ℕ :=
  packedTime p+C (k+74)*(X+packedTime p+3)+3

lemma result_correct {n : ℕ} (hn : 0<n) (w : List (ConstraintGate n)) :
    (result hn w).2≠0 ∧ RationalAccumulator.value (result hn w)=constraintCircuitMatrix w (zeroBits n) (zeroBits n) := by
  refine ⟨RationalAccumulator.run_nonzero _ _ (by decide) (SourceSampleIntegers.items_nonzero hn 0 w),?_⟩
  rw [result,SourceOuter.result,RationalAccumulator.run_value _ _ (by decide) (SourceSampleIntegers.items_nonzero hn 0 w),SourceSampleIntegers.items_value]
  simp [RationalAccumulator.value]

lemma metadata_executes (g : BitString→ℕ) {n : ℕ} (w : List (ConstraintGate n)) :
    ∃c,metadata.Executes g (Function.update (fun _ : Fin 64=>[]) 0 (circuitBits n w))
      (SourceFrontend.rawStore w 0 (List.replicate n true)) c ∧ c≤CircuitMetadata.time.eval (circuitBits n w).length := by
  obtain ⟨c,hc,hb⟩:=CircuitMetadata.on_executes metadataMap g (Function.update (fun _ : Fin 64=>[]) 0 (circuitBits n w)) w
    (by funext i;fin_cases i <;> rfl)
  refine ⟨c,?_,hb⟩
  convert hc using 1
  funext i;fin_cases i <;> rfl

lemma outer_executes {k : ℕ} (W : OracleBlock k) (g : BitString→ℕ) (p : Polynomial ℕ)
    (hW : SourceWordCall.WordSolverSpec W g p) {n : ℕ} (hn : 0<n) (w : List (ConstraintGate n)) :
    ∃c,(SourceOuter.program W).Executes g (SourceOuter.state (k:=k) w 0 0 (0,1))
      (SourceOuter.state (k:=k) w 0 0 (result hn w)) c ∧ c≤((SourceOuter.time p).comp outerBound).eval (circuitBits n w).length := by
  have hbit:=SourceQueryEnumeration.bitBound hn 0 w (0,1) 0 (by decide)
  simp only [Nat.zero_add,Nat.add_zero] at hbit
  obtain ⟨c,hc,hb,ht⟩:=SourceOuter.program_executes W g p hW hn 0 w (0,1) []
    (SourceQueryEnumeration.prefixBitSize.eval (circuitBits n w).length) (by simpa only [List.append_nil] using hbit)
  exact ⟨c,hc,by simpa only [outerBound,eval_comp,eval_add,eval_X,Nat.add_zero] using hb⟩
end HiddenCircuits.Circuit.Runtime.ConstraintZero
