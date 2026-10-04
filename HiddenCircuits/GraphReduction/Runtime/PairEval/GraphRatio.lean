import HiddenCircuits.GraphReduction.Runtime.PairEval.GraphRecovery
import HiddenCircuits.GraphReduction.Runtime.WordGraph.CliqueRatioCell

/-! The one-level probe ratio is computed by finite integer programs. Two
physical unit registers replace the absent outer interpolation factor. -/
namespace HiddenCircuits.GraphReduction.Runtime.PairEval.GraphRatio
open Complexity OracleBlock BinaryArithmetic Polynomial WordGraph
open RatioCell (state fields)
set_option maxHeartbeats 1000000

noncomputable def ones : OracleBlock 52 := seq (push 9 true) (seq (push 9 false) (seq (push 10 true) (push 10 false)))
noncomputable def right (kind : GraphRecovery.Kind) : OracleBlock 52 :=
  match kind with | none => RatioCell.right | some _ => CliqueRatioCell.right
noncomputable def norm (kind : GraphRecovery.Kind) : OracleBlock 52 :=
  match kind with | none => RatioCell.norm | some b => CliqueRatioCell.norm b
noncomputable def program (kind : GraphRecovery.Kind) : OracleBlock 52 :=
  seq ones (seq (right kind) (seq (norm kind) (seq RatioCell.copyAnswer RatioCell.combine)))
noncomputable def rightTime (kind : GraphRecovery.Kind) : Polynomial ℕ :=
  match kind with | none => GridWeightsRuntime.pairTime | some _ => EvenWeightsRuntime.time
noncomputable def normTime (kind : GraphRecovery.Kind) : Polynomial ℕ :=
  match kind with | none => RatioNormalization.time | some _ => OddFactorialNormalization.time

def componentBound (kind : GraphRecovery.Kind) (w : PairInput) (s : GraphRecovery.Index w) (answer B : ℕ) : Prop :=
  RegisterMachine.Bounded B (RatioCombine.registers (GraphRecovery.sign kind w) (answer:ℤ)
    1 (GraphRecovery.numerator kind w s) 1 (GraphRecovery.denominator kind w s) (GraphRecovery.normalization kind w s))
noncomputable def costBound (kind : GraphRecovery.Kind) (w : PairInput) (s : GraphRecovery.Index w) (answer B : ℕ) : ℕ :=
  (rightTime kind).eval (GraphRecovery.degree w)+(normTime kind).eval (s.val+w.pairs.length+w.particles)+
  5*(signedBits (answer:ℤ)).length+RatioCombine.time.eval B+20

lemma ones_executes (g : BitString→ℕ) (s l p h : ℕ) (answer : BitString) :
    ones.Executes g (state 0 0 s l p h answer [] [] (fields [] [] [] [] [] [] []))
      (state 0 0 s l p h answer [] [] (fields (signedBits 1) (signedBits 1) [] [] [] [] [])) 10 := by
  let st := state 0 0 s l p h answer [] [] (fields [] [] [] [] [] [] [])
  have a := push_executes g (9:Fin 53) true st
  have b := push_executes g (9:Fin 53) false (Function.update st 9 [true])
  have c := push_executes g (10:Fin 53) true (Function.update (Function.update st 9 [true]) 9 [false,true])
  have d := push_executes g (10:Fin 53) false (Function.update (Function.update (Function.update st 9 [true]) 9 [false,true]) 10 [true])
  convert seq_executes _ _ g a (seq_executes _ _ g b (seq_executes _ _ g c d)) using 1
  funext i;fin_cases i <;> rfl

lemma right_executes (g : BitString→ℕ) (kind : GraphRecovery.Kind) (w : PairInput) (s : GraphRecovery.Index w) (answer : BitString) :
    ∃c,(right kind).Executes g
      (state 0 0 s.val (GraphRecovery.degree w-s.val) w.particles w.pairs.length answer [] [] (fields (signedBits 1) (signedBits 1) [] [] [] [] []))
      (state 0 0 s.val (GraphRecovery.degree w-s.val) w.particles w.pairs.length answer [] []
        (fields (signedBits 1) (signedBits 1) (signedBits (GraphRecovery.denominator kind w s)) (signedBits (GraphRecovery.numerator kind w s)) [] [] [])) c ∧
      c ≤ (rightTime kind).eval (GraphRecovery.degree w) := by
  cases kind with
  | none => exact RatioCell.right_executes g _ s 0 0 _ _ answer _ _
  | some b => exact CliqueRatioCell.right_executes g _ s 0 0 _ _ answer _ _

lemma norm_executes (g : BitString→ℕ) (kind : GraphRecovery.Kind) (w : PairInput) (s : GraphRecovery.Index w) (answer : BitString) :
    ∃c,(norm kind).Executes g
      (state 0 0 s.val (GraphRecovery.degree w-s.val) w.particles w.pairs.length answer [] []
        (fields (signedBits 1) (signedBits 1) (signedBits (GraphRecovery.denominator kind w s)) (signedBits (GraphRecovery.numerator kind w s)) [] [] []))
      (state 0 0 s.val (GraphRecovery.degree w-s.val) w.particles w.pairs.length answer [] []
        (fields (signedBits 1) (signedBits 1) (signedBits (GraphRecovery.denominator kind w s)) (signedBits (GraphRecovery.numerator kind w s))
          (signedBits (GraphRecovery.normalization kind w s)) (signedBits (GraphRecovery.sign kind w)) [])) c ∧
      c ≤ (normTime kind).eval (s.val+w.pairs.length+w.particles) := by
  cases kind with
  | none => exact RatioCell.norm_executes g 0 0 _ _ _ _ answer _ _ _ _
  | some b =>
    have h := CliqueRatioCell.norm_executes g b 0 0 s.val (GraphRecovery.degree w-s.val) w.particles w.pairs.length answer
      (signedBits 1) (signedBits 1) (signedBits (GraphRecovery.denominator (some b) w s)) (signedBits (GraphRecovery.numerator (some b) w s))
    cases b <;> simpa only [norm,normTime,GraphRecovery.normalization,GraphRecovery.sign,OddFactorialNormalization.exponent,OddFactorialNormalization.signValue] using h

theorem program_executes (g : BitString→ℕ) (kind : GraphRecovery.Kind) (w : PairInput) (s : GraphRecovery.Index w) (answer B : ℕ)
    (hB : componentBound kind w s answer B) :
    ∃c,(program kind).Executes g
      (state 0 0 s.val (GraphRecovery.degree w-s.val) w.particles w.pairs.length (signedBits (answer:ℤ)) [] [] (fields [] [] [] [] [] [] []))
      (state 0 0 s.val (GraphRecovery.degree w-s.val) w.particles w.pairs.length (signedBits (answer:ℤ))
        (signedBits (GraphRecovery.ratio kind w s answer).1) (signedBits (GraphRecovery.ratio kind w s answer).2) (fields [] [] [] [] [] [] [])) c ∧
      c ≤ costBound kind w s answer B := by
  have ha := ones_executes g s.val (GraphRecovery.degree w-s.val) w.particles w.pairs.length (signedBits (answer:ℤ))
  obtain ⟨b,hb,hbb⟩ := right_executes g kind w s (signedBits (answer:ℤ))
  obtain ⟨c,hc,hcb⟩ := norm_executes g kind w s (signedBits (answer:ℤ))
  have hd := RatioCell.copyAnswer_executes g 0 0 s.val (GraphRecovery.degree w-s.val) w.particles w.pairs.length (signedBits (answer:ℤ))
    (signedBits 1) (signedBits 1) (signedBits (GraphRecovery.denominator kind w s)) (signedBits (GraphRecovery.numerator kind w s))
    (signedBits (GraphRecovery.normalization kind w s)) (signedBits (GraphRecovery.sign kind w))
  obtain ⟨e,he,heb⟩ := RatioCell.combine_executes g 0 0 s.val (GraphRecovery.degree w-s.val) w.particles w.pairs.length (answer:ℤ)
    1 (GraphRecovery.numerator kind w s) 1 (GraphRecovery.denominator kind w s) (GraphRecovery.normalization kind w s) (GraphRecovery.sign kind w) B hB
  simp only [mul_one,one_mul] at he
  exact ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb (seq_executes _ _ g hc (seq_executes _ _ g hd he))),by unfold costBound;omega⟩
end HiddenCircuits.GraphReduction.Runtime.PairEval.GraphRatio
