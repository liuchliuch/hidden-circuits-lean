import HiddenCircuits.Approximation.SelfReduction.Runtime.RobustLoop
import HiddenCircuits.Approximation.SelfReduction.Runtime.MaxLoop

/-! Execution of robust maximum selection using the score vector and register embedding. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
set_option maxHeartbeats 800000

def scoreVector (n : ℕ) (q : Fin (n+1) → ℕ) (radius : ℕ) (i : Fin (n+1)) : ℕ :=
  (naturalCluster n q radius i).card

def maximumScoresEmbedding : Fin 11 ↪ Fin 16 where
  toFun i := if i.val<3 then ⟨i.val,by omega⟩ else if i.val=3 then 14 else ⟨i.val-1,by omega⟩
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

noncomputable def maximumScores : OracleBlock 15 := rename maximumScan maximumScoresEmbedding
noncomputable def robustSelectScores : OracleBlock 15 :=
  seq (copyOn 13 14 4 (by decide) (by decide) (by decide))
    (seq robustScores (seq (clear 1) maximumScores))

 theorem scoreVector_le (n : ℕ) (q : Fin (n+1) → ℕ) (radius : ℕ) (i : Fin (n+1)) :
    scoreVector n q radius i ≤ n+1 := by
  unfold scoreVector naturalCluster
  exact (Finset.card_filter_le _ _).trans (by simp)

 theorem score_list_eq (n : ℕ) (q : Fin (n+1) → ℕ) (radius : ℕ) :
    (List.ofFn q).map (fun y => neighborhoodCount y radius (List.ofFn q)) =
      List.ofFn (scoreVector n q radius) := by
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  exact neighborhoodCount_ofFn n q radius i

 theorem maximumScores_executes (g : BitString → ℕ) (n radius : ℕ) (q : Fin (n+1) → ℕ) :
    let scores := scoreVector n q radius
    let j := chooseMax n scores
    ∃ t, maximumScores.Executes g
      (robustStore 0 0 0 [] (unaryValues (List.ofFn q)) (unaryValues (List.ofFn scores)) [])
      (robustStore (scores j) j.val (n+1) [] (unaryValues (List.ofFn q)) [] []) t ∧
      t ≤ 1+(n+1)*(50*((n+1)+n+2)) := by
  dsimp only
  obtain ⟨t,ht,hb⟩ := maximumScan_chooseMax g n (n+1) (scoreVector n q radius)
    (scoreVector_le n q radius)
  refine ⟨t,?_,hb⟩
  apply rename_executes_to maximumScan maximumScoresEmbedding g ht
  · funext i; fin_cases i <;> simp [robustStore,maxStore,maximumScoresEmbedding,unaryValues]
  · funext i; fin_cases i <;> simp [robustStore,maxStore,maximumScoresEmbedding]
  · intro i hi; fin_cases i
    all_goals first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl) | exact False.elim (hi 3 rfl)

 theorem robustSelectScores_executes (g : BitString → ℕ) (n radius B : ℕ) (q : Fin (n+1) → ℕ)
    (hq : ∀ i, q i ≤ B) :
    let scores := scoreVector n q radius
    let j := chooseMax n scores
    ∃ t, robustSelectScores.Executes g
      (robustStore 0 radius 0 [] (unaryValues (List.ofFn q)) [] [])
      (robustStore (scores j) j.val (n+1) [] (unaryValues (List.ofFn q)) [] []) t ∧
      t ≤ 1000*(n+2)^2*(B+radius+1)+100 := by
  dsimp only
  have hcopy : (copyOn (13 : Fin 16) 14 4 (by decide) (by decide) (by decide)).Executes g
      (robustStore 0 radius 0 [] (unaryValues (List.ofFn q)) [] [])
      (robustStore 0 radius 0 [] (unaryValues (List.ofFn q)) (unaryValues (List.ofFn q)) [])
      (5*(unaryValues (List.ofFn q)).length+2) := by
    convert copyOn_executes g (13 : Fin 16) 14 4 (by decide) (by decide) (by decide)
      (robustStore 0 radius 0 [] (unaryValues (List.ofFn q)) [] []) rfl using 1
    funext i; fin_cases i <;> simp [robustStore]
  obtain ⟨ts,hs,hbs⟩ := robustScores_executes g (List.ofFn q) radius B
    (by intro x hx; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx; exact hq i)
  rw [score_list_eq] at hs
  have hc : (clear (1 : Fin 16)).Executes g
      (robustStore 0 radius 0 [] (unaryValues (List.ofFn q)) (unaryValues (List.ofFn (scoreVector n q radius))) [])
      (robustStore 0 0 0 [] (unaryValues (List.ofFn q)) (unaryValues (List.ofFn (scoreVector n q radius))) []) (radius+1) := by
    convert clear_executes g (1 : Fin 16)
      (robustStore 0 radius 0 [] (unaryValues (List.ofFn q)) (unaryValues (List.ofFn (scoreVector n q radius))) []) using 1
    · funext i; fin_cases i <;> rfl
    · simp [robustStore]
  obtain ⟨tm,hm,hbm⟩ := maximumScores_executes g n radius q
  have hlen : (unaryValues (List.ofFn q)).length ≤ 2*(n+1)*(B+1) := by
    exact (unaryValues_length_bound _ B (by intro x hx; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx; exact hq i)).trans_eq (by simp)
  simp only [List.length_ofFn] at hbs
  refine ⟨_,seq_executes _ _ g hcopy (seq_executes _ _ g hs (seq_executes _ _ g hc hm)),?_⟩
  nlinarith

end HiddenCircuits.Approximation.SelfReduction.Runtime
