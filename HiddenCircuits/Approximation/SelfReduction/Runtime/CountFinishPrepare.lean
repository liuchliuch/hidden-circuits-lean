import HiddenCircuits.Approximation.SelfReduction.Runtime.CountCoreFrame

/-! Physical transfer from the adaptive-loop result into the estimator-output
assembler. Unused coins and random-width storage are cleared explicitly. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open Complexity Complexity.OracleBlock

def finishSource (coins graph : BitString) (width M T cap groups : ℕ) (out alive : BitString) (d N : ℕ) : Store 72 := fun i =>
  if i.val=0 then coins else if i.val=2 then List.replicate width true else if i.val=59 then List.replicate M true
  else if i.val=62 then List.replicate (8*T) true else if i.val=63 then List.replicate cap true
  else if i.val=64 then List.replicate groups true else if i.val=65 then graph else if i.val=66 then List.replicate T true
  else if i.val=68 then out else if i.val=70 then alive else if i.val=71 then List.replicate d true
  else if i.val=72 then List.replicate N true else []

theorem finishSource_eq (coins graph : BitString) (width M T cap groups : ℕ) (out alive : BitString) (d N : ℕ) :
    finishSource coins graph width M T cap groups out alive d N=
      coreStore (countStore coins [] graph width M T cap groups 0 out alive 0 0) d N := by
  funext i; fin_cases i <;> rfl

def finishTarget (graph : BitString) (M d T cap groups N : ℕ) (out alive : BitString) : Store 72 := fun i =>
  if i.val=0 then List.replicate M true else if i.val=1 then List.replicate d true
  else if i.val=2 then out.reverse else if i.val=3 then alive
  else if i.val=62 then List.replicate (8*T) true else if i.val=63 then List.replicate cap true
  else if i.val=64 then List.replicate groups true else if i.val=65 then graph else if i.val=66 then List.replicate T true
  else if i.val=72 then List.replicate N true else []

noncomputable def finishPrepare : OracleBlock 72 :=
  seq (clear 0) (seq (moveOn 59 0 4 (by decide) (by decide) (by decide))
    (seq (moveOn 71 1 4 (by decide) (by decide) (by decide)) (seq (clear 2)
      (seq (reverseOn 68 2 (by decide)) (moveOn 70 3 4 (by decide) (by decide) (by decide))))))

set_option maxHeartbeats 800000 in
 theorem finishPrepare_executes (g : BitString → ℕ) (coins graph : BitString) (width M T cap groups : ℕ)
    (out alive : BitString) (d N : ℕ) :
    finishPrepare.Executes g (finishSource coins graph width M T cap groups out alive d N)
      (finishTarget graph M d T cap groups N out alive)
      (coins.length+6*M+6*d+width+2*out.length+6*alive.length+28) := by
  let s0 := finishSource coins graph width M T cap groups out alive d N
  let s1 := Function.update s0 (0 : Fin 73) []
  let s2 := Function.update (Function.update s1 (59 : Fin 73) []) (0 : Fin 73) (List.replicate M true)
  let s3 := Function.update (Function.update s2 (71 : Fin 73) []) (1 : Fin 73) (List.replicate d true)
  let s4 := Function.update s3 (2 : Fin 73) []
  let s5 := Function.update (Function.update s4 (68 : Fin 73) []) (2 : Fin 73) out.reverse
  have h1 : (clear (0 : Fin 73)).Executes g s0 s1 (coins.length+1) := clear_executes g _ s0
  have h2 : (moveOn (59 : Fin 73) 0 4 (by decide) (by decide) (by decide)).Executes g s1 s2 (6*M+5) := by
    convert moveOn_executes g (59 : Fin 73) 0 4 (by decide) (by decide) (by decide) s1 rfl using 1
    · funext i; fin_cases i <;> simp [s0,s1,s2,finishSource]
    · simp [s0,s1,finishSource]
  have h3 : (moveOn (71 : Fin 73) 1 4 (by decide) (by decide) (by decide)).Executes g s2 s3 (6*d+5) := by
    convert moveOn_executes g (71 : Fin 73) 1 4 (by decide) (by decide) (by decide) s2 rfl using 1
    · funext i; fin_cases i <;> simp [s0,s1,s2,s3,finishSource]
    · simp [s0,s1,s2,finishSource]
  have h4 : (clear (2 : Fin 73)).Executes g s3 s4 (width+1) := by
    convert clear_executes g (2 : Fin 73) s3 using 1
    simp [s0,s1,s2,s3,finishSource]
  have h5 : (reverseOn (68 : Fin 73) 2 (by decide)).Executes g s4 s5 (2*out.length+1) := by
    convert reverseOn_executes g (68 : Fin 73) 2 (by decide) s4 using 1
    · funext i; fin_cases i <;> simp [s0,s1,s2,s3,s4,s5,finishSource]
  have h6 : (moveOn (70 : Fin 73) 3 4 (by decide) (by decide) (by decide)).Executes g s5
      (finishTarget graph M d T cap groups N out alive) (6*alive.length+5) := by
    convert moveOn_executes g (70 : Fin 73) 3 4 (by decide) (by decide) (by decide) s5 rfl using 1
    funext i; fin_cases i <;> simp [s0,s1,s2,s3,s4,s5,finishSource,finishTarget]
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3
    (seq_executes _ _ g h4 (seq_executes _ _ g h5 h6)))) using 1 <;> omega

 theorem finishPrepare_queryFree : finishPrepare.QueryFree :=
  seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (clear_queryFree _)
      (seq_queryFree _ _ (reverseOn_queryFree _ _ _) (moveOn_queryFree _ _ _ _ _ _)))))

end HiddenCircuits.Approximation.SelfReduction.Runtime
