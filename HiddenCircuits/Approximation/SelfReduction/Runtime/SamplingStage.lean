import HiddenCircuits.Approximation.SelfReduction.Runtime.SampleGroupLoop
import HiddenCircuits.Approximation.SelfReduction.Runtime.BranchSelect

/-! One complete literal sampling/counting deletion stage. Fresh random blocks
are consumed, real sampler calls are executed, and the empirical maximum is
returned. Persistent graph context and every global unary parameter survive. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

def stageSamplePorts : Fin 62 ↪ Fin 65 where
  toFun i := i.castAdd 3
  inj' := by intro i j h; exact Fin.ext (congrArg (fun x : Fin 65 => x.val) h)

def stageBranchPorts : Fin 21 ↪ Fin 65 where
  toFun i := if i.val=0 then 7 else if i.val=1 then 8 else if i.val=17 then 62
    else if i.val=18 then 6 else if i.val=19 then 60 else if i.val=20 then 9
    else ⟨i.val+8,by omega⟩
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

def stageStore (coins context : BitString) (width batch radius cap groups clock : ℕ)
    (matrix : BitString) (value idx : ℕ) : Store 64 := fun i =>
  if i.val=0 then coins else if i.val=1 then context else if i.val=2 then List.replicate width true
  else if i.val=6 then matrix else if i.val=7 then List.replicate value true
  else if i.val=8 then List.replicate idx true else if i.val=59 then List.replicate batch true
  else if i.val=60 then List.replicate clock true else if i.val=62 then List.replicate radius true
  else if i.val=63 then List.replicate cap true else if i.val=64 then List.replicate groups true else []

noncomputable def samplingStage : OracleBlock 64 :=
  seq (copyOn 64 60 3 (by decide) (by decide) (by decide))
    (seq (rename sampleGroups stageSamplePorts)
      (seq (copyOn 63 60 3 (by decide) (by decide) (by decide))
        (seq (push 7 true) (seq (rename branchSelect stageBranchPorts) (clear 6)))))

noncomputable def samplingStageBound (C b n width M B radius dataLength : ℕ) : ℕ :=
  (n+1)*sampleGroupBound C width M B+4*(n+1)*(2*M*(B+1)+1)+4+
  ((b+1)*branchIterationBound n M B radius (b+1) dataLength+
    4*(b+1)*(M+1)+(b+1)*(50*(M+b+2))+2*b+16)+
    5*(n+1)+5*(b+1)+dataLength+16

set_option maxHeartbeats 800000 in
 theorem samplingStage_executes (g : BitString → ℕ) (context rest : BitString)
    (b n width batch B radius : ℕ) (blocks : Fin (n+1) → List BitString)
    (hM : ∀ i, (blocks i).length=batch) (hw : ∀ i, ∀ bits ∈ blocks i, bits.length=width)
    (hB : ∀ i, ∀ word ∈ sampledWords context (blocks i), word.length ≤ B) :
    let matrix := groupWords (List.ofFn (fun i => sampledWords context (blocks i)))
    let q : Fin (b+1) → ℕ := fun i => branchBoostValue n radius (fun j => sampledWords context (blocks j)) i.val
    ∃ t, samplingStage.Executes g
      (stageStore ((List.ofFn blocks).flatten.flatten++rest) context width batch radius (b+1) (n+1) 0 [] 0 0)
      (stageStore rest context width batch radius (b+1) (n+1) 0 [] (q (chooseMax b q)) (chooseMax b q).val) t ∧
      t ≤ samplingStageBound context.length b n width batch B radius matrix.length := by
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
  have h1 : (copyOn (64 : Fin 65) 60 3 (by decide) (by decide) (by decide)).Executes g s0 s1 (5*(n+1)+2) := by
    convert copyOn_executes g (64 : Fin 65) 60 3 (by decide) (by decide) (by decide) s0 rfl using 1
    · funext i; fin_cases i <;> simp [s0,s1,stageStore]
    · simp [s0,stageStore]
  obtain ⟨ts,hs,hbs⟩ := sampleGroups_executes g context rest (List.ofFn blocks) width batch B
    (by intro xs hx; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx; exact hM i)
    (by intro xs hx; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx; exact hw i)
    (by intro xs hx; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx; exact hB i)
  have h2 : (rename sampleGroups stageSamplePorts).Executes g s1 s2 ts := by
    apply rename_executes_to sampleGroups stageSamplePorts g hs
    · funext i; fin_cases i <;> simp [s1,stageStore,sampleGridStore,stageSamplePorts]
    · funext i; fin_cases i <;> simp [s2,stageStore,sampleGridStore,stageSamplePorts,matrix,List.map_ofFn,Function.comp_def]
    · intro j hj
      have h0 : j.val≠0 := by intro h; exact hj 0 (Fin.ext h.symm)
      have h6 : j.val≠6 := by intro h; exact hj 6 (Fin.ext h.symm)
      have h60 : j.val≠60 := by intro h; exact hj 60 (Fin.ext h.symm)
      simp [s1,s2,stageStore,h0,h6,h60]
  have h3 : (copyOn (63 : Fin 65) 60 3 (by decide) (by decide) (by decide)).Executes g s2 s3 (5*(b+1)+2) := by
    convert copyOn_executes g (63 : Fin 65) 60 3 (by decide) (by decide) (by decide) s2 rfl using 1
    · funext i; fin_cases i <;> simp [s2,s3,stageStore]
    · simp [s2,stageStore]
  have h4 : (push (7 : Fin 65) true).Executes g s3 s4 1 := by
    convert push_executes g (7 : Fin 65) true s3 using 1
    funext i; fin_cases i <;> simp [s3,s4,stageStore]
  obtain ⟨tb,hb,hbb⟩ := branchSelect_executes g b n batch B radius (fun i => sampledWords context (blocks i))
    (by intro i; simp [sampledWords,hM i]) hB
  have h5 : (rename branchSelect stageBranchPorts).Executes g s4 s5 tb := by
    apply rename_executes_to branchSelect stageBranchPorts g hb
    · funext i; fin_cases i <;> simp [s4,stageStore,branchStore,stageBranchPorts,matrix]
    · funext i; fin_cases i <;> simp [s5,stageStore,selectedStore,stageBranchPorts,matrix,q]
    · intro j hj; fin_cases j
      all_goals first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) | exact False.elim (hj 19 rfl)
  have h6 : (clear (6 : Fin 65)).Executes g s5 sf (matrix.length+1) := by
    convert clear_executes g (6 : Fin 65) s5 using 1
    funext i; fin_cases i <;> simp [s5,sf,stageStore]
  simp only [List.length_ofFn] at hbs
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3
    (seq_executes _ _ g h4 (seq_executes _ _ g h5 h6)))),?_⟩
  dsimp only [samplingStageBound,matrix]
  omega

end HiddenCircuits.Approximation.SelfReduction.Runtime
