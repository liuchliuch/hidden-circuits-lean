import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphSamplingLayout

/-! Exact execution of the concrete general-graph sampling stage. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.GraphSampling
open Complexity Complexity.OracleBlock

set_option maxHeartbeats 800000 in
 theorem stage_executes (g : BitString → ℕ) (context rest : BitString)
    (b n width batch B radius : ℕ) (blocks : Fin (n+1) → List BitString)
    (hM : ∀ i, (blocks i).length=batch) (hw : ∀ i, ∀ bits ∈ blocks i, bits.length=width)
    (hB : ∀ i, ∀ word ∈ sampledWords context (blocks i), word.length ≤ B) :
    let matrix := groupWords (List.ofFn (fun i => sampledWords context (blocks i)))
    let q : Fin (b+1) → ℕ := fun i => branchBoostValue n radius (fun j => sampledWords context (blocks j)) i.val
    ∃ t, stage.Executes g
      (stageStore ((List.ofFn blocks).flatten.flatten++rest) context width batch radius (b+1) (n+1) 0 [] 0 0)
      (stageStore rest context width batch radius (b+1) (n+1) 0 [] (q (chooseMax b q)) (chooseMax b q).val) t ∧
      t ≤ stageBound context.length b n width batch B radius matrix.length := by
  dsimp only
  let matrix := groupWords (List.ofFn (fun i => sampledWords context (blocks i)))
  let q : Fin (b+1) → ℕ := fun i => branchBoostValue n radius (fun j => sampledWords context (blocks j)) i.val
  let s0 := stageStore ((List.ofFn blocks).flatten.flatten++rest) context width batch radius (b+1) (n+1) 0 [] 0 0
  let s1 := stageStore ((List.ofFn blocks).flatten.flatten++rest) context width batch radius (b+1) (n+1) (n+1) [] 0 0
  let s2 := stageStore rest context width batch radius (b+1) (n+1) 0 matrix 0 0
  let s3 := stageStore rest context width batch radius (b+1) (n+1) (b+1) matrix 0 0
  let s4 := stageStore rest context width batch radius (b+1) (n+1) (b+1) matrix 1 0
  let s5 := stageStore rest context width batch radius (b+1) (n+1) 0 matrix (q (chooseMax b q)) (chooseMax b q).val
  let sf := stageStore rest context width batch radius (b+1) (n+1) 0 [] (q (chooseMax b q)) (chooseMax b q).val
  have h1 : (copyOn (64 : Fin 99) 60 3 (by decide) (by decide) (by decide)).Executes g s0 s1 (5*(n+1)+2) := by
    convert copyOn_executes g (64 : Fin 99) 60 3 (by decide) (by decide) (by decide) s0 rfl using 1
    · funext i; fin_cases i <;> first | rfl | simp [s0,s1,stageStore]
    · simp [s0,stageStore]
  obtain ⟨ts,hs,hbs⟩ := sampleGroups_executes g context rest (List.ofFn blocks) width batch B
    (by intro xs hx; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx; exact hM i)
    (by intro xs hx; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx; exact hw i)
    (by intro xs hx; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx; exact hB i)
  have h2 : (rename sampleGroups stageSamplePorts).Executes g s1 s2 ts := by
    apply rename_executes_to sampleGroups stageSamplePorts g hs
    · funext i; fin_cases i <;> first | rfl | simp [s1,stageStore,sampleGridStore,stageSamplePorts]
    · funext i; fin_cases i <;> first | rfl | simp [s2,stageStore,sampleGridStore,stageSamplePorts,matrix,List.map_ofFn,Function.comp_def]
    · intro j hj
      have h0 : j.val≠0 := by intro h; exact hj 0 (Fin.ext h.symm)
      have h6 : j.val≠6 := by intro h; exact hj 6 (Fin.ext h.symm)
      have h60 : j.val≠60 := by intro h; exact hj 60 (Fin.ext h.symm)
      simp [s1,s2,stageStore,h0,h6,h60]
  have h3 : (copyOn (63 : Fin 99) 60 3 (by decide) (by decide) (by decide)).Executes g s2 s3 (5*(b+1)+2) := by
    convert copyOn_executes g (63 : Fin 99) 60 3 (by decide) (by decide) (by decide) s2 rfl using 1
    · funext i; fin_cases i <;> first | rfl | simp [s2,s3,stageStore]
    · simp [s2,stageStore]
  have h4 : (push (7 : Fin 99) true).Executes g s3 s4 1 := by
    convert push_executes g (7 : Fin 99) true s3 using 1
    funext i; fin_cases i <;> first | rfl | simp [s3,s4,stageStore]
  obtain ⟨tb,hb,hbb⟩ := branchSelect_executes g b n batch B radius (fun i => sampledWords context (blocks i))
    (by intro i; simp [sampledWords,hM i]) hB
  have h5 : (rename branchSelect stageBranchPorts).Executes g s4 s5 tb := by
    apply rename_executes_to branchSelect stageBranchPorts g hb
    · funext i; fin_cases i <;> first | rfl | simp [s4,stageStore,branchStore,stageBranchPorts,Runtime.stageBranchPorts,matrix]
    · funext i; fin_cases i <;> first | rfl | simp [s5,stageStore,selectedStore,stageBranchPorts,Runtime.stageBranchPorts,matrix,q]
    · intro j hj; fin_cases j
      all_goals first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) | exact False.elim (hj 19 rfl)
  have h6 : (clear (6 : Fin 99)).Executes g s5 sf (matrix.length+1) := by
    convert clear_executes g (6 : Fin 99) s5 using 1
    funext i; fin_cases i <;> first | rfl | simp [s5,sf,stageStore]
  simp only [List.length_ofFn] at hbs
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3
    (seq_executes _ _ g h4 (seq_executes _ _ g h5 h6)))),?_⟩
  dsimp only [stageBound,matrix]
  omega

theorem stageBound_mono (C C' b n m M B radius L L' : ℕ) (hC : C ≤ C') (hL : L ≤ L') :
    stageBound C b n m M B radius L ≤ stageBound C' b n m M B radius L' := by
  dsimp only [stageBound,sampleGroupBound,branchIterationBound]
  gcongr
  exact polynomial_nat_eval_mono _ (by omega)

end HiddenCircuits.Approximation.SelfReduction.Runtime.GraphSampling
