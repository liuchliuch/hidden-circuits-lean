import HiddenCircuits.Circuit.Runtime.DeltaWordInterpolation
import HiddenCircuits.Circuit.Runtime.DeltaWordSetup
import HiddenCircuits.Circuit.Runtime.WordEvalHardness
import HiddenCircuits.Complexity.BinaryArithmetic.RationalNormalizeRuntime
import HiddenCircuits.Complexity.PairSerialization

/-! The positive-width independent Delta-to-Word evaluator. Its interpolation
loop is initialized by a physical parse, and the final ratio is normalized by
the actual binary Euclidean algorithm to the native rational oracle encoding. -/
namespace HiddenCircuits.Circuit.Runtime.DeltaWordZero
open Complexity OracleBlock BinaryArithmetic Polynomial

def initial (xs : BitString) : Store 65 := Function.update (fun _=>[]) 0 xs
def lowMap : Fin 64 ↪ Fin 66 := (SourceWordCall.lowEmbedding 0).trans (FramedFor.embedding 64)
noncomputable def setup : OracleBlock 65 := rename (rename DeltaWordSetup.program (SourceWordCall.lowEmbedding 0)) (FramedFor.embedding 64)
noncomputable def core : OracleBlock 65 := seq setup (DeltaWordInterpolation.program WordEvalOracle.program)
noncomputable def coreTime : Polynomial ℕ := DeltaWordSetup.time+DeltaWordInterpolation.time WordEvalOracle.time+2

def pairMap : Fin 3 ↪ Fin 66 where
  toFun i:=![12,11,24] i
  inj':=by decide +kernel
noncomputable def pair : OracleBlock 65 := PairSerialization.on pairMap
noncomputable def packed : OracleBlock 65 := seq core pair
noncomputable def cleanup : OracleBlock 65 := cleanResult 12 24 (by decide) (by decide)
noncomputable def ratioProgram : OracleBlock 65 := seq packed cleanup
noncomputable def packedTime : Polynomial ℕ := coreTime+10*(X+coreTime)+11
noncomputable def ratioTime : Polynomial ℕ := packedTime+70*(X+packedTime+3)+3

def normalizationMap : Fin 16 ↪ Fin 66 :=
  ⟨fun i=>⟨i.val,by omega⟩,by intro i j h;exact Fin.ext (congrArg (fun z : Fin 66=>z.val) h)⟩
noncomputable def normalize : OracleBlock 65 := rename RationalNormalize.rawProgram normalizationMap
noncomputable def program : OracleBlock 65 := seq ratioProgram normalize
noncomputable def time : Polynomial ℕ := ratioTime+RationalNormalize.rawTime.comp (X+ratioTime)+2
noncomputable def result {n : ℕ} (hn : 0<n) (w : List (DeltaGate n)) := DeltaWordInterpolation.result hn w

def ratioBits (z : RationalAccumulator.Ratio) : BitString := pairBits (signedBits z.1) (signedBits z.2)
lemma initial_bound (xs : BitString) : ∀i,(initial xs i).length≤xs.length := by
  intro i;simp only [initial,Function.update_apply];split_ifs <;> simp

lemma frame_initial (xs : BitString) :
    FramedFor.frame (SourceWordCall.lifted (k:=0) (DeltaWordSetup.initial xs)) []=initial xs := by
  unfold DeltaWordSetup.initial SourceWordCall.lifted
  rw [←SourceWordCall.update_low,←FramedFor.update_body]
  have hz : SourceWordCall.store (fun _ : Fin 64=>([]:BitString)) (fun _ : Fin 1=>[])=
      (fun _ : Fin 65=>[]) := by
    funext i;simp [SourceWordCall.store]
  rw [hz,SourceReduction.FramedFor.frame_empty]
  rfl

set_option maxHeartbeats 1200000 in
lemma setup_executes (g : BitString→ℕ) {n : ℕ} (w : List (DeltaGate n)) :
    ∃c,setup.Executes g (initial (DeltaWordEmitter.circuitBits n w))
      (DeltaWordInterpolation.state (k:=0) w 0 (0,1)) c ∧ c≤DeltaWordSetup.time.eval (DeltaWordEmitter.circuitBits n w).length := by
  obtain ⟨c,hc,hb⟩:=DeltaWordSetup.program_executes g w
  have hh:=FramedFor.lift_executes _ g _ _ [] c (SourceWordCall.lift_executes (k:=0) _ g _ _ c hc)
  refine ⟨c,?_,hb⟩
  rw [frame_initial] at hh
  exact hh

lemma core_executes (g : BitString→ℕ) (hg : WordEvalOracle.oracleSpec g) {n : ℕ} (hn : 0<n) (w : List (DeltaGate n)) :
    ∃c,core.Executes g (initial (DeltaWordEmitter.circuitBits n w))
      (DeltaWordInterpolation.state (k:=0) w 0 (result hn w)) c ∧ c≤coreTime.eval (DeltaWordEmitter.circuitBits n w).length := by
  obtain ⟨a,ha,hab⟩:=setup_executes g w
  obtain ⟨b,hb,hbb⟩:=DeltaWordInterpolation.program_executes_polynomial WordEvalOracle.program g WordEvalOracle.time
    (WordEvalOracle.solverSpec g hg) hn w
  refine ⟨a+b+2,seq_executes _ _ g ha hb,?_⟩
  simp only [coreTime,eval_add,eval_ofNat];omega

set_option maxHeartbeats 1000000 in
lemma state_pair {n : ℕ} (w : List (DeltaGate n)) (z : RationalAccumulator.Ratio) :
    DeltaWordInterpolation.state (k:=0) w 0 z∘pairMap=PairSerialization.state (signedBits z.2) (signedBits z.1) [] := by
  funext i;fin_cases i <;> rfl

lemma packed_executes (g : BitString→ℕ) (hg : WordEvalOracle.oracleSpec g) {n : ℕ} (hn : 0<n) (w : List (DeltaGate n)) :
    ∃s c,packed.Executes g (initial (DeltaWordEmitter.circuitBits n w)) s c ∧ s 12=ratioBits (result hn w) ∧
      c≤packedTime.eval (DeltaWordEmitter.circuitBits n w).length := by
  obtain ⟨a,ha,hab⟩:=core_executes g hg hn w
  let z:=result hn w
  have hp:=PairSerialization.on_executes pairMap g (DeltaWordInterpolation.state (k:=0) w 0 z)
    (signedBits z.1) (signedBits z.2) (state_pair w z)
  have hs:=ha.stack_bound (initial_bound (DeltaWordEmitter.circuitBits n w)) (11:Fin 66)
  change (signedBits z.1).length≤(DeltaWordEmitter.circuitBits n w).length+a at hs
  refine ⟨_,a+(10*(signedBits z.1).length+9)+2,seq_executes _ _ g ha hp,?_,?_⟩
  · simp only [pairMap,Matrix.cons_val_zero,Function.update_self];rfl
  · simp only [packedTime,eval_add,eval_mul,eval_X,eval_ofNat];omega

lemma ratioProgram_executes (g : BitString→ℕ) (hg : WordEvalOracle.oracleSpec g) {n : ℕ} (hn : 0<n) (w : List (DeltaGate n)) :
    ∃c,ratioProgram.Executes g (initial (DeltaWordEmitter.circuitBits n w)) (initial (ratioBits (result hn w))) c ∧
      c≤ratioTime.eval (DeltaWordEmitter.circuitBits n w).length := by
  obtain ⟨s,a,ha,hs,hab⟩:=packed_executes g hg hn w
  obtain ⟨b,hb,hbb⟩:=cleanResult_executes g (12:Fin 66) 24 (by decide) (by decide) (by decide)
    s ((DeltaWordEmitter.circuitBits n w).length+a) (ha.stack_bound (initial_bound _))
  rw [hs] at hb
  refine ⟨a+b+2,seq_executes _ _ g ha hb,?_⟩
  simp only [ratioTime,eval_add,eval_mul,eval_X,eval_ofNat]
  nlinarith

lemma normalize_executes (g : BitString→ℕ) (z : RationalAccumulator.Ratio) :
    ∃c,normalize.Executes g (initial (ratioBits z))
      (initial (RationalOracleEncoding.bits (RationalAccumulator.value z))) c ∧ c≤RationalNormalize.rawTime.eval (ratioBits z).length := by
  obtain ⟨c,hc,hb⟩:=RationalNormalize.on_executes normalizationMap g (initial (ratioBits z)) (ratioBits z)
    (by funext i;fin_cases i <;> rfl)
  refine ⟨c,?_,hb⟩
  simpa only [ratioBits,RationalNormalize.rawValue_pair,show normalizationMap 0=0 from rfl,initial,Function.update_idem,RationalAccumulator.value] using hc

/-- A single actual finite oracle machine evaluates every canonical positive
width Delta circuit and returns the canonical natural-coded rational answer. -/
theorem program_executes (g : BitString→ℕ) (hg : WordEvalOracle.oracleSpec g) {n : ℕ} (hn : 0<n) (w : List (DeltaGate n)) :
    ∃c,program.Executes g (initial (DeltaWordEmitter.circuitBits n w))
      (initial (RationalOracleEncoding.bits (deltaCircuitMatrix w (zeroBits n) (zeroBits n)))) c ∧
      c≤time.eval (DeltaWordEmitter.circuitBits n w).length := by
  obtain ⟨a,ha,hab⟩:=ratioProgram_executes g hg hn w
  obtain ⟨b,hb,hbb⟩:=normalize_executes g (result hn w)
  have he : RationalAccumulator.value (result hn w)=deltaCircuitMatrix w (zeroBits n) (zeroBits n):=
    (DeltaWordInterpolation.result_correct hn w).2
  rw [he] at hb
  have hs:=ha.stack_bound (initial_bound _) (0:Fin 66)
  change (ratioBits (result hn w)).length≤(DeltaWordEmitter.circuitBits n w).length+a at hs
  have hm:=polynomial_nat_eval_mono RationalNormalize.rawTime (hs.trans (Nat.add_le_add_left hab _))
  dsimp only at hm
  refine ⟨a+b+2,seq_executes _ _ g ha hb,?_⟩
  simp only [time,eval_add,eval_comp,eval_X,eval_ofNat];omega
end HiddenCircuits.Circuit.Runtime.DeltaWordZero
