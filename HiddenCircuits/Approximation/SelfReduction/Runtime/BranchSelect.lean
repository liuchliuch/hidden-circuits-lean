import HiddenCircuits.Approximation.SelfReduction.Runtime.BranchBoostLoop
import HiddenCircuits.Approximation.SelfReduction.Runtime.MaxLoop

/-! Complete actual statistical branch choice: every confidence estimate is
computed from the sample matrix, then the literal maximum scan returns its
value and partner index with the proved deterministic tie convention. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

def branchMaxPorts : Fin 11 ↪ Fin 21 where
  toFun i := i.castAdd 10
  inj' := by intro i j h; exact Fin.ext (congrArg (fun x : Fin 21 => x.val) h)

def selectedStore (value idx radius : ℕ) (data : BitString) : Store 20 := fun i =>
  if i.val=0 then List.replicate value true else if i.val=1 then List.replicate idx true
  else if i.val=17 then List.replicate radius true else if i.val=18 then data else []

noncomputable def branchFinalize : OracleBlock 20 :=
  seq (clear 0) (seq (reverseOn 20 3 (by decide)) (seq (rename maximumScan branchMaxPorts) (clear 2)))
noncomputable def branchSelect : OracleBlock 20 := seq branchBoostLoop branchFinalize

 theorem branchFinalize_executes (g : BitString → ℕ) (b M radius : ℕ) (data : BitString)
    (q : Fin (b+1) → ℕ) (hq : ∀ i, q i ≤ M) :
    ∃ t, branchFinalize.Executes g
      (branchStore (b+1) radius 0 data (unaryValues (List.ofFn q)).reverse 0)
      (selectedStore (q (chooseMax b q)) (chooseMax b q).val radius data) t ∧
      t ≤ 4*(b+1)*(M+1)+(b+1)*(50*(M+b+2))+2*b+13 := by
  let s0 := branchStore (b+1) radius 0 data (unaryValues (List.ofFn q)).reverse 0
  let s1 := Function.update s0 (0 : Fin 21) []
  let s2 := Function.update (Function.update s1 (20 : Fin 21) []) (3 : Fin 21) (unaryValues (List.ofFn q))
  let sf := selectedStore (q (chooseMax b q)) (chooseMax b q).val radius data
  let s3 := Function.update sf (2 : Fin 21) (List.replicate (b+1) true)
  have h1 : (clear (0 : Fin 21)).Executes g s0 s1 (b+3) := by
    convert clear_executes g (0 : Fin 21) s0 using 1
    simp [s0,branchStore]
  have h2 : (reverseOn (20 : Fin 21) 3 (by decide)).Executes g s1 s2
      (2*(unaryValues (List.ofFn q)).length+1) := by
    convert reverseOn_executes g (20 : Fin 21) 3 (by decide) s1 using 1
    · funext i; fin_cases i <;> simp [s0,s1,s2,branchStore]
    · simp [s0,s1,branchStore]
  obtain ⟨tm,hm,hbm⟩ := maximumScan_chooseMax g b M q hq
  have h3 : (rename maximumScan branchMaxPorts).Executes g s2 s3 tm := by
    apply rename_executes_to maximumScan branchMaxPorts g hm
    · funext i; fin_cases i <;> simp [s0,s1,s2,branchStore,branchMaxPorts,maxStore,unaryValues]
    · funext i; fin_cases i <;> simp [s3,sf,selectedStore,branchMaxPorts,maxStore]
    · intro j hj; fin_cases j
      all_goals first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) | exact False.elim (hj 2 rfl) | exact False.elim (hj 3 rfl)
  have h4 : (clear (2 : Fin 21)).Executes g s3 sf (b+2) := by
    convert clear_executes g (2 : Fin 21) s3 using 1
    · funext i; fin_cases i <;> simp [s3,sf,selectedStore]
    · simp [s3]
  have hlen : (unaryValues (List.ofFn q)).length ≤ 2*(b+1)*(M+1) := by
    exact (unaryValues_length_bound _ M (by intro x hx; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx; exact hq i)).trans_eq (by simp)
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)),?_⟩
  nlinarith

 theorem branchSelect_executes (g : BitString → ℕ) (b n M B radius : ℕ)
    (groups : Fin (n+1) → List BitString) (hM : ∀ i, (groups i).length ≤ M)
    (hB : ∀ i, ∀ x ∈ groups i, x.length ≤ B) :
    let q : Fin (b+1) → ℕ := fun i => branchBoostValue n radius groups i.val
    ∃ t, branchSelect.Executes g (branchStore 0 radius (b+1) (groupWords (List.ofFn groups)) [] 0)
      (selectedStore (q (chooseMax b q)) (chooseMax b q).val radius (groupWords (List.ofFn groups))) t ∧
      t ≤ (b+1)*branchIterationBound n M B radius (b+1) (groupWords (List.ofFn groups)).length+
        4*(b+1)*(M+1)+(b+1)*(50*(M+b+2))+2*b+16 := by
  dsimp only
  obtain ⟨tl,hl,hbl⟩ := branchBoostLoop_executes g n M B radius (b+1) groups hM hB
  obtain ⟨tf,hf,hbf⟩ := branchFinalize_executes g b M radius (groupWords (List.ofFn groups))
    (fun i => branchBoostValue n radius groups i.val) (fun i => branchBoostValue_le n radius M groups hM i.val)
  refine ⟨_,seq_executes _ _ g hl hf,?_⟩
  omega

end HiddenCircuits.Approximation.SelfReduction.Runtime
