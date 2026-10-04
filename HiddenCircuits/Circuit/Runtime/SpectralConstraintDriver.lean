import HiddenCircuits.Circuit.Runtime.SpectralConstraintZero
import HiddenCircuits.Circuit.Runtime.BoundaryPreprocessFinish

namespace HiddenCircuits.Circuit.Runtime.SpectralConstraintEvaluation
open Complexity OracleBlock BinaryArithmetic Polynomial
abbrev initial:=SpectralConstraint.initial

def boundaryMap : Fin 8 ↪ Fin 68:=⟨fun i=>⟨i.val,by omega⟩,
  by intro i j h;exact Fin.ext (congrArg (fun z : Fin 68=>z.val) h)⟩
noncomputable def preprocess : OracleBlock 67:=rename BoundaryPreprocess.program boundaryMap
noncomputable def program : OracleBlock 67:=seq preprocess SpectralConstraint.program
noncomputable def time : Polynomial ℕ:=BoundaryPreprocess.time+
  SpectralConstraint.time.comp (X+BoundaryPreprocess.time)+2

lemma preprocess_executes (g : BitString→ℕ) {n : ℕ} (w : List (ConstraintGate n)) (x y : CodeBits n) :
    ∃c,preprocess.Executes g (initial (BoundaryTransport.inputBits w x y))
      (initial (circuitBits n (zeroBoundaryCircuit w x y))) c ∧
      c ≤ BoundaryPreprocess.time.eval (BoundaryTransport.inputBits w x y).length := by
  obtain ⟨c,hc,hb⟩:=BoundaryPreprocess.program_executes g (BoundaryTransport.mask n x)
    (BoundaryTransport.mask n y) (List.replicate n true) (encodeBitList (w.map gateBits))
  rw [show BoundaryPreprocess.result (BoundaryTransport.mask n x) (BoundaryTransport.mask n y)
    (List.replicate n true) (encodeBitList (w.map gateBits))=circuitBits n (zeroBoundaryCircuit w x y) from BoundaryTransport.output_correct w x y] at hc
  refine ⟨c,?_,hb⟩
  apply rename_executes_to _ boundaryMap g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have hz:i≠0:=by intro h;subst i;exact hi 0 rfl
    simp [initial,SpectralConstraint.initial,hz]

theorem program_executes (g : BitString→ℕ) (hg : DeltaOracle g) {n : ℕ}
    (w : List (ConstraintGate n)) (x y : CodeBits n) :
    ∃c,program.Executes g (initial (BoundaryTransport.inputBits w x y))
      (initial (RationalOracleEncoding.bits (constraintCircuitMatrix w x y))) c ∧
      c ≤ time.eval (BoundaryTransport.inputBits w x y).length := by
  obtain ⟨a,ha,hab⟩:=preprocess_executes g w x y
  obtain ⟨b,hb,hbb⟩:=SpectralConstraint.program_executes g hg (zeroBoundaryCircuit w x y)
  rw [zeroBoundaryCircuit_correct] at hb
  have hs:=ha.stack_bound (SpectralConstraint.initial_bound _) (0:Fin 68)
  change (circuitBits n (zeroBoundaryCircuit w x y)).length ≤ (BoundaryTransport.inputBits w x y).length+a at hs
  have hm:=polynomial_nat_eval_mono SpectralConstraint.time (hs.trans (Nat.add_le_add_left hab _))
  dsimp only at hm
  refine ⟨a+b+2,seq_executes _ _ g ha hb,?_⟩
  simp only [time,eval_add,eval_comp,eval_X,eval_ofNat]
  omega

theorem native_executes (g : BitString→ℕ) (hg : DeltaOracle g) (C : ConstraintInput) :
    ∃c,program.Executes g (initial C.encode)
      (initial (Computability.encodeNat (RationalOracleEncoding.code C.value))) c ∧ c ≤ time.eval C.encode.length := by
  simpa only [RationalOracleEncoding.encode_code] using program_executes g hg C.gates C.source C.target
end HiddenCircuits.Circuit.Runtime.SpectralConstraintEvaluation
