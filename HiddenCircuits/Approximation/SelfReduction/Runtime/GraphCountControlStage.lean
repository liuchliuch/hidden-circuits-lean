import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountControlFrame
import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphSamplingStage

/-! The concrete general-graph sampler stage embedded around all adaptive-count
control registers and the saved original dimension/input size. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
open Complexity Complexity.OracleBlock

noncomputable def stage : OracleBlock 106 := rename GraphSampling.stage stagePorts

 theorem stage_executes (g : BitString → ℕ) (context rest graph out alive : BitString)
    (b n width M B T depth originalDepth N : ℕ) (blocks : Fin (n+1) → List BitString)
    (hM : ∀ i, (blocks i).length=M) (hw : ∀ i, ∀ bits ∈ blocks i, bits.length=width)
    (hB : ∀ i, ∀ word ∈ GraphSampling.sampledWords context (blocks i), word.length ≤ B) :
    let matrix := groupWords (List.ofFn (fun i => GraphSampling.sampledWords context (blocks i)))
    let q : Fin (b+1) → ℕ := fun i => branchBoostValue n (8*T)
      (fun j => GraphSampling.sampledWords context (blocks j)) i.val
    ∃ t, stage.Executes g
      (store (coreStore (countStore ((List.ofFn blocks).flatten.flatten++rest) context graph width M T (b+1) (n+1)
        depth out alive 0 0) originalDepth N))
      (store (coreStore (countStore rest context graph width M T (b+1) (n+1) depth out alive
        (q (chooseMax b q)) (chooseMax b q).val) originalDepth N)) t ∧
      t ≤ GraphSampling.stageBound context.length b n width M B (8*T) matrix.length := by
  dsimp only
  obtain ⟨t,ht,hb⟩ := GraphSampling.stage_executes g context rest b n width M B (8*T) blocks hM hw hB
  refine ⟨t,?_,hb⟩
  apply rename_executes_to GraphSampling.stage stagePorts g ht
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · intro j hj; fin_cases j
    all_goals first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 7 rfl) | exact False.elim (hj 8 rfl)

end HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
