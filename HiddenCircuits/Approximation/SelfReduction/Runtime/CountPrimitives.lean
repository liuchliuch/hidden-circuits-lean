import HiddenCircuits.Approximation.SelfReduction.Runtime.CountFrame

/-! Preparation and the two real control outcomes of a counting iteration. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open Complexity Complexity.OracleBlock
open GraphReduction.MonotoneEndpointEncoding

 theorem countPrepare_executes (g : BitString → ℕ) (coins graph : BitString)
    (width batch T cap groups depth : ℕ) (out alive : BitString) :
    countPrepare.Executes g (countStore coins [] graph width batch T cap groups depth out alive 0 0)
      (countStore coins (sampleInput graph T) graph width batch T cap groups depth out alive 0 0)
      (5*T+13*graph.length+15) := by
  have h := contextPrepareOn_executes countContextPorts g
    (countStore coins [] graph width batch T cap groups depth out alive 0 0) graph T (by
      funext i; fin_cases i <;> rfl)
  convert h using 1
  funext i; fin_cases i <;> rfl

 theorem countReject_executes (g : BitString → ℕ) (coins context graph : BitString)
    (width batch T cap groups depth idx : ℕ) (out : BitString) :
    countReject.Executes g (countStore coins context graph width batch T cap groups depth out [true] 0 idx)
      (countStore coins [] graph width batch T cap groups 0 out [] 0 0)
      (depth+idx+context.length+11) := by
  let s0 := countStore coins context graph width batch T cap groups depth out [true] 0 idx
  let s1 := countStore coins context graph width batch T cap groups 0 out [true] 0 idx
  let s2 := countStore coins context graph width batch T cap groups 0 out [] 0 idx
  let s3 := countStore coins context graph width batch T cap groups 0 out [] 0 0
  let sf := countStore coins [] graph width batch T cap groups 0 out [] 0 0
  have h1 : (clear (67 : Fin 71)).Executes g s0 s1 (depth+1) := by
    convert clear_executes g (67 : Fin 71) s0 using 1
    · funext i; fin_cases i <;> rfl
    · simp [s0]
  have h2 : (clear (70 : Fin 71)).Executes g s1 s2 2 := by
    convert clear_executes g (70 : Fin 71) s1 using 1
    funext i; fin_cases i <;> rfl
  have h3 : (clear (8 : Fin 71)).Executes g s2 s3 (idx+1) := by
    convert clear_executes g (8 : Fin 71) s2 using 1
    · funext i; fin_cases i <;> rfl
    · simp [s2]
  have h4 : (clear (1 : Fin 71)).Executes g s3 sf (context.length+1) := by
    convert clear_executes g (1 : Fin 71) s3 using 1
    funext i; fin_cases i <;> rfl
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)) using 1 <;> omega

 theorem countAccept_executes (g : BitString → ℕ) {d : ℕ} (E : MonotoneEndpoints (d+1)) (j : Fin (d+1))
    (coins context : BitString) (width batch T cap groups depth c : ℕ) (out : BitString) :
    ∃ t, countAccept.Executes g
      (countStore coins context (encode ⟨d+1,E⟩) width batch T cap groups depth out [true] c j.val)
      (countStore coins [] (encode ⟨d,SamplerRuntime.EndpointFiber.deleteFirst E j⟩) width batch T cap groups depth
        ((true::pairBits (List.replicate (c+1) true) []).reverse++out) [true] 0 0) t ∧
      t ≤ 1000*(d+2)^2+9*(c+1)+j.val+context.length+18 := by
  let graph := encode ⟨d+1,E⟩
  let graph' := encode ⟨d,SamplerRuntime.EndpointFiber.deleteFirst E j⟩
  let out' := (true::pairBits (List.replicate (c+1) true) []).reverse++out
  let s0 := countStore coins context graph width batch T cap groups depth out [true] c j.val
  let s1 := countStore coins context graph width batch T cap groups depth out [true] (c+1) j.val
  let s2 := countStore coins context graph width batch T cap groups depth out' [true] 0 j.val
  let s3 := countStore coins context graph' width batch T cap groups depth out' [true] 0 j.val
  let s4 := countStore coins context graph' width batch T cap groups depth out' [true] 0 0
  let sf := countStore coins [] graph' width batch T cap groups depth out' [true] 0 0
  have h1 : (push (7 : Fin 71) true).Executes g s0 s1 1 := by
    convert push_executes g (7 : Fin 71) true s0 using 1
    funext i; fin_cases i <;> simp [s0,s1,countStore,countFrame,stageStore,List.replicate_succ] <;> rfl
  have h2 : (emitUnaryReversed (7 : Fin 71) 68).Executes g s1 s2 (9*(c+1)+7) := by
    convert emitUnaryReversed_executes g (7 : Fin 71) 68 (by decide) s1 using 1
    · funext i; fin_cases i <;> simp [s1,s2,out'] <;> rfl
    · simp [s1]
  obtain ⟨tr,hr,hbr⟩ := EndpointResidual.programOn_executes countResidualPorts g s2 E j (by
    funext i; fin_cases i <;> rfl)
  have h3 : countResidual.Executes g s2 s3 tr := by
    convert hr using 1
    funext i; fin_cases i <;> rfl
  have h4 : (clear (8 : Fin 71)).Executes g s3 s4 (j.val+1) := by
    convert clear_executes g (8 : Fin 71) s3 using 1
    · funext i; fin_cases i <;> rfl
    · simp [s3]
  have h5 : (clear (1 : Fin 71)).Executes g s4 sf (context.length+1) := by
    convert clear_executes g (1 : Fin 71) s4 using 1
    funext i; fin_cases i <;> rfl
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 (seq_executes _ _ g h4 h5))),?_⟩
  omega

end HiddenCircuits.Approximation.SelfReduction.Runtime
