import HiddenCircuits.Approximation.SelfReduction.Runtime.GroupTallyLoop
import HiddenCircuits.Approximation.SelfReduction.Runtime.RobustSelect

/-! Real confidence boosting for one target partner, preserving the target and
radius for the enclosing branch loop. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

def boostCountPorts : Fin 14 ↪ Fin 18 where
  toFun i := i.castAdd 4
  inj' := by intro i j h; exact Fin.ext (congrArg (fun x : Fin 18 => x.val) h)
def boostSelectPorts : Fin 16 ↪ Fin 18 where
  toFun i := ⟨i.val+1,by omega⟩
  inj' := by intro i j h; apply Fin.ext; have hh := congrArg (fun x : Fin 18 => x.val) h; simp at hh; omega

def boostStore (target data : BitString) (radius value : ℕ) : Store 17 := fun i =>
  if i.val=0 then target else if i.val=1 then List.replicate value true else if i.val=10 then data
  else if i.val=17 then List.replicate radius true else []

noncomputable def groupBoost : OracleBlock 17 :=
  seq (rename groupCounts boostCountPorts)
    (seq (moveOn 10 14 3 (by decide) (by decide) (by decide))
      (seq (copyOn 17 2 3 (by decide) (by decide) (by decide)) (rename robustSelect boostSelectPorts)))

 def groupBoostValue (n radius : ℕ) (target : BitString) (groups : Fin (n+1) → List BitString) : ℕ :=
  let c := fun i => wordOccurrences target (groups i)
  c (chooseMax n (scoreVector n c radius))

 theorem groupBoost_executes (g : BitString → ℕ) (n M B radius : ℕ) (target : BitString)
    (groups : Fin (n+1) → List BitString) (hM : ∀ i, (groups i).length ≤ M)
    (hB : ∀ i, ∀ x ∈ groups i, x.length ≤ B) :
    ∃ t, groupBoost.Executes g (boostStore target (groupWords (List.ofFn groups)) radius 0)
      (boostStore target [] radius (groupBoostValue n radius target groups)) t ∧
      t ≤ (n+1)*(110*(M+1)*(B+target.length+1))+12*(n+1)*(M+1)+
        5*radius+2000*(n+2)^2*(M+radius+1)+217 := by
  let counts := unaryValues (List.ofFn (fun i => wordOccurrences target (groups i)))
  let s1 := boostStore target counts radius 0
  let s2 := Function.update (Function.update s1 (10 : Fin 18) []) (14 : Fin 18) counts
  let s3 := Function.update s2 (2 : Fin 18) (List.replicate radius true)
  obtain ⟨tc,hc,hbc⟩ := groupCounts_executes g target (List.ofFn groups) M B
    (by intro xs hx; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx; exact hM i)
    (by intro xs hx; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx; exact hB i)
  have h1 : (rename groupCounts boostCountPorts).Executes g
      (boostStore target (groupWords (List.ofFn groups)) radius 0) s1 tc := by
    apply rename_executes_to groupCounts boostCountPorts g hc
    · funext i; fin_cases i <;> simp [boostStore,groupStore,boostCountPorts]
    · funext i; fin_cases i <;> simp [s1,counts,boostStore,groupStore,boostCountPorts,List.map_ofFn,Function.comp_def]
    · intro j hj; fin_cases j
      all_goals first | rfl | exact False.elim (hj 10 rfl)
  have h2 : (moveOn (10 : Fin 18) 14 3 (by decide) (by decide) (by decide)).Executes g s1 s2
      (6*counts.length+5) := by
    convert moveOn_executes g (10 : Fin 18) 14 3 (by decide) (by decide) (by decide) s1 rfl using 1
    · funext i; fin_cases i <;> simp [s1,s2,boostStore]
  have h3 : (copyOn (17 : Fin 18) 2 3 (by decide) (by decide) (by decide)).Executes g s2 s3
      (5*radius+2) := by
    convert copyOn_executes g (17 : Fin 18) 2 3 (by decide) (by decide) (by decide) s2 rfl using 1
    · funext i; fin_cases i <;> simp [s1,s2,s3,boostStore]
    · simp [s1,s2,boostStore]
  have hq (i) : wordOccurrences target (groups i) ≤ M := List.countP_le_length.trans (hM i)
  obtain ⟨tr,hr,hbr⟩ := robustSelect_executes g n radius M (fun i => wordOccurrences target (groups i)) hq
  have h4 : (rename robustSelect boostSelectPorts).Executes g s3
      (boostStore target [] radius (groupBoostValue n radius target groups)) tr := by
    apply rename_executes_to robustSelect boostSelectPorts g hr
    · funext i; fin_cases i <;> simp [s1,s2,s3,boostStore,boostSelectPorts,robustStore,counts]
    · funext i; fin_cases i <;> simp [boostStore,boostSelectPorts,robustStore,groupBoostValue]
    · intro j hj; fin_cases j
      all_goals first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) | exact False.elim (hj 13 rfl)
  have hlen : counts.length ≤ 2*(n+1)*(M+1) := by
    exact (unaryValues_length_bound _ M (by intro c hc; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc; exact hq i)).trans_eq (by simp)
  simp only [List.length_ofFn] at hbc
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)),?_⟩
  nlinarith

end HiddenCircuits.Approximation.SelfReduction.Runtime
