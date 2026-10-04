import HiddenCircuits.Circuit.Runtime.DeltaWordZero
import HiddenCircuits.Circuit.Runtime.DeltaWordBoundaryEncoding

/-! Independent Lemma 7.1: one fixed finite machine evaluates canonical native
Delta circuits through WordEval, with arbitrary boundary states and zero wires.
Both query and answer lengths are charged by its OracleBlock semantics. -/
namespace HiddenCircuits.Circuit.Runtime.DeltaWordEvaluation
open Complexity OracleBlock BinaryArithmetic Polynomial

def initial (input : BitString) : Store 65 := Function.update (fun _=>[]) 0 input
def smallMap : Fin 8 ↪ Fin 66 :=
  ⟨fun i=>⟨i.val,by omega⟩,by intro i j h;exact Fin.ext (congrArg (fun z : Fin 66=>z.val) h)⟩
noncomputable def preprocess : OracleBlock 65 := rename DeltaBoundary.preprocess smallMap
noncomputable def positive : OracleBlock 65 := seq preprocess DeltaWordZero.program
noncomputable def zero : OracleBlock 65 := seq (clear 0) (prepend 0 (RationalOracleEncoding.bits 1))
noncomputable def program : OracleBlock 65 := branchPop 0 zero zero (seq (push 0 true) positive)
noncomputable def positiveTime : Polynomial ℕ := DeltaBoundary.preprocessTime+
  DeltaWordZero.time.comp (X+DeltaBoundary.preprocessTime)+2
noncomputable def time : Polynomial ℕ := positiveTime+35

lemma preprocess_executes (g : BitString→ℕ) {n : ℕ} (w : List (DeltaGate n)) (x y : CodeBits n) :
    ∃c,preprocess.Executes g (initial (DeltaBoundary.inputBits w x y))
      (initial (DeltaWordEmitter.circuitBits n (DeltaBoundary.zeroBoundaryCircuit w x y))) c ∧
      c≤DeltaBoundary.preprocessTime.eval (DeltaBoundary.inputBits w x y).length := by
  obtain ⟨c,hc,hb⟩:=DeltaBoundary.preprocess_executes g w x y
  refine ⟨c,?_,hb⟩
  apply rename_executes_to _ smallMap g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have hz:i≠0:=by intro h;subst i;exact hi 0 rfl
    simp [initial,hz]
lemma positive_executes (g : BitString→ℕ) (hg : WordEvalOracle.oracleSpec g) {n : ℕ} (hn : 0<n)
    (w : List (DeltaGate n)) (x y : CodeBits n) :
    ∃c,positive.Executes g (initial (DeltaBoundary.inputBits w x y))
      (initial (RationalOracleEncoding.bits (deltaCircuitMatrix w x y))) c ∧
      c≤positiveTime.eval (DeltaBoundary.inputBits w x y).length := by
  obtain ⟨a,ha,hab⟩:=preprocess_executes g w x y
  obtain ⟨b,hb,hbb⟩:=DeltaWordZero.program_executes g hg hn (DeltaBoundary.zeroBoundaryCircuit w x y)
  rw [DeltaBoundary.zeroBoundaryCircuit_correct] at hb
  have hs:=ha.stack_bound (DeltaWordZero.initial_bound (DeltaBoundary.inputBits w x y)) (0:Fin 66)
  change (DeltaWordEmitter.circuitBits n (DeltaBoundary.zeroBoundaryCircuit w x y)).length≤(DeltaBoundary.inputBits w x y).length+a at hs
  have hm:=polynomial_nat_eval_mono DeltaWordZero.time (hs.trans (Nat.add_le_add_left hab _))
  dsimp only at hm
  refine ⟨a+b+2,seq_executes _ _ g ha hb,?_⟩
  simp only [positiveTime,eval_add,eval_comp,eval_X,eval_ofNat];omega

theorem program_executes (g : BitString→ℕ) (hg : WordEvalOracle.oracleSpec g)
    (n : ℕ) (w : List (DeltaGate n)) (x y : CodeBits n) :
    ∃c,program.Executes g (initial (DeltaBoundary.inputBits w x y))
      (initial (RationalOracleEncoding.bits (deltaCircuitMatrix w x y))) c ∧
      c≤time.eval (DeltaBoundary.inputBits w x y).length := by
  cases n with
  | zero=>
    rw [DeltaBoundary.inputBits_zero,DeltaBoundary.matrix_entry_zero_wires]
    have hc : (clear (0:Fin 66)).Executes g (initial [false,false]) (initial []) 3 := by
      convert clear_executes g (0:Fin 66) (initial [false,false]) using 1
      funext i;simp [initial]
    have hp : (prepend (0:Fin 66) (RationalOracleEncoding.bits 1)).Executes g (initial [])
        (initial (RationalOracleEncoding.bits 1)) 22 := by
      convert prepend_executes g (0:Fin 66) (RationalOracleEncoding.bits 1) (initial []) using 1
      funext i;simp [initial]
    refine ⟨29,?_,?_⟩
    · apply branchPop_false 0 _ _ _ g (rest:=[false,false]) (by rfl)
      convert seq_executes _ _ g hc hp using 1
      funext i;simp [initial]
    · simp only [time,eval_add,eval_ofNat];omega
  | succ n=>
    obtain ⟨c,hc,hb⟩:=positive_executes g hg (by omega : 0<n+1) w x y
    let rest:=decide (x.1=1)::pairBits (BoundaryTransport.mask n x.2)
      (pairBits (BoundaryTransport.mask (n+1) y) (DeltaWordEmitter.circuitBits (n+1) w))
    have hin : DeltaBoundary.inputBits w x y=true::rest := rfl
    have hp : (push (0:Fin 66) true).Executes g (initial rest) (initial (DeltaBoundary.inputBits w x y)) 1 := by
      convert push_executes g (0:Fin 66) true (initial rest) using 1
      funext i;simp [initial,hin]
    refine ⟨1+c+2+2,?_,?_⟩
    · apply branchPop_true 0 _ _ _ g (rest:=rest) (by exact hin)
      convert seq_executes _ _ g hp hc using 1
      funext i;simp [initial,hin]
    · simp only [time,eval_add,eval_ofNat];omega

/-- Native natural-coded rational output; there is no noncanonical ratio proxy. -/
theorem native_executes (g : BitString→ℕ) (hg : WordEvalOracle.oracleSpec g) (C : DeltaInput) :
    ∃c,program.Executes g (initial C.encode)
      (initial (Computability.encodeNat (RationalOracleEncoding.code C.value))) c ∧ c≤time.eval C.encode.length := by
  simpa only [RationalOracleEncoding.encode_code] using program_executes g hg C.wires C.gates C.source C.target
end HiddenCircuits.Circuit.Runtime.DeltaWordEvaluation
