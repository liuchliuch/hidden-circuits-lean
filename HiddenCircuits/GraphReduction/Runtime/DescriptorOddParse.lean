import HiddenCircuits.GraphReduction.Runtime.WordGraph.PairEncoding
import HiddenCircuits.Complexity.OracleRepeat

namespace HiddenCircuits.GraphReduction.Runtime.DescriptorOddParse
open Complexity OracleBlock BinaryArithmetic
set_option maxHeartbeats 600000

def state (data tag index rev : BitString) : Store 3 := ![data,tag,index,rev]
noncomputable def bit : OracleBlock 3 := branchPop 0 skip (push 3 false) (push 3 true)
noncomputable def four : OracleBlock 3 := seq bit (seq bit (seq bit bit))
noncomputable def program : OracleBlock 3 := seq four (seq (reverseOn 0 2 (by decide))
  (seq (reverseOn 3 1 (by decide)) (prepend 1 [true,false])))

lemma bit_executes (g : BitString → ℕ) (b : Bool) (rest acc : BitString) :
    bit.Executes g (state (b::rest) [] [] acc) (state rest [] [] (b::acc)) 3 := by
  have hu : Function.update (state (b::rest) [] [] acc) (0:Fin 4) rest=state rest [] [] acc := by funext i;fin_cases i <;> rfl
  have hp : (push (3:Fin 4) b).Executes g (state rest [] [] acc) (state rest [] [] (b::acc)) 1 := by
    convert push_executes g (3:Fin 4) b (state rest [] [] acc) using 1
    funext i;fin_cases i <;> rfl
  cases b
  · apply branchPop_false 0 skip (push 3 false) (push 3 true) g rfl
    rw [hu];exact hp
  · apply branchPop_true 0 skip (push 3 false) (push 3 true) g rfl
    rw [hu];exact hp

lemma four_executes (g : BitString → ℕ) (a b c d : Bool) (rest : BitString) :
    four.Executes g (state (a::b::c::d::rest) [] [] []) (state rest [] [] [d,c,b,a]) 18 :=
  seq_executes _ _ g (bit_executes g a (b::c::d::rest) [])
    (seq_executes _ _ g (bit_executes g b (c::d::rest) [a])
      (seq_executes _ _ g (bit_executes g c (d::rest) [b,a]) (bit_executes g d rest [c,b,a])))

theorem program_executes (g : BitString → ℕ) (C : CutCode) :
    program.Executes g (state ([C.leftRise,C.leftDrop,C.rightRise,C.rightDrop]++List.replicate C.index true) [] [] [])
      (state [] [true,false,C.leftRise,C.leftDrop,C.rightRise,C.rightDrop] (List.replicate C.index true) []) (2*C.index+41) := by
  have h₁ := four_executes g C.leftRise C.leftDrop C.rightRise C.rightDrop (List.replicate C.index true)
  have h₂ : (reverseOn (0:Fin 4) 2 (by decide)).Executes g
      (state (List.replicate C.index true) [] [] [C.rightDrop,C.rightRise,C.leftDrop,C.leftRise])
      (state [] [] (List.replicate C.index true) [C.rightDrop,C.rightRise,C.leftDrop,C.leftRise]) (2*C.index+1) := by
    convert reverseOn_executes g (0:Fin 4) 2 (by decide)
      (state (List.replicate C.index true) [] [] [C.rightDrop,C.rightRise,C.leftDrop,C.leftRise]) using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state]
  have h₃ : (reverseOn (3:Fin 4) 1 (by decide)).Executes g
      (state [] [] (List.replicate C.index true) [C.rightDrop,C.rightRise,C.leftDrop,C.leftRise])
      (state [] [C.leftRise,C.leftDrop,C.rightRise,C.rightDrop] (List.replicate C.index true) []) 9 := by
    convert reverseOn_executes g (3:Fin 4) 1 (by decide)
      (state [] [] (List.replicate C.index true) [C.rightDrop,C.rightRise,C.leftDrop,C.leftRise]) using 1
    funext i;fin_cases i <;> rfl
  have h₄ : (prepend (1:Fin 4) [true,false]).Executes g
      (state [] [C.leftRise,C.leftDrop,C.rightRise,C.rightDrop] (List.replicate C.index true) [])
      (state [] [true,false,C.leftRise,C.leftDrop,C.rightRise,C.rightDrop] (List.replicate C.index true) []) 7 := by
    convert prepend_executes g (1:Fin 4) [true,false]
      (state [] [C.leftRise,C.leftDrop,C.rightRise,C.rightDrop] (List.replicate C.index true) []) using 1
    funext i;fin_cases i <;> rfl
  convert seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ h₄)) using 1 <;> omega
lemma bit_queryFree : bit.QueryFree := branchPop_queryFree _ _ _ _ skip_queryFree (push_queryFree _ _) (push_queryFree _ _)
lemma program_queryFree : program.QueryFree := seq_queryFree _ _
  (seq_queryFree _ _ bit_queryFree (seq_queryFree _ _ bit_queryFree (seq_queryFree _ _ bit_queryFree bit_queryFree)))
  (seq_queryFree _ _ (reverseOn_queryFree _ _ _) (seq_queryFree _ _ (reverseOn_queryFree _ _ _) (prepend_queryFree _ _)))
end HiddenCircuits.GraphReduction.Runtime.DescriptorOddParse
