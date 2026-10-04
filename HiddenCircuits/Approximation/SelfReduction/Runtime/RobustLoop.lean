import HiddenCircuits.Approximation.SelfReduction.Runtime.RobustBody

/-! The actual nested loops
compute every neighborhood score and restore its input order by bit reversal. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
set_option maxHeartbeats 800000

noncomputable def robustScores : OracleBlock 15 :=
  seq (whilePop 14 skip robustBody) (reverseOn 15 14 (by decide))

theorem robustScores_execution (g : BitString → ℕ) (xs ys : List ℕ) (radius B : ℕ)
    (hxs : ∀ x ∈ xs, x ≤ B) (hys : ∀ y ∈ ys, y ≤ B) (out : BitString) :
    ∃ t, WhileExecution (14 : Fin 16) skip robustBody g
      (robustStore 0 radius 0 [] (unaryValues xs) (unaryValues ys) out)
      (robustStore 0 radius 0 [] (unaryValues xs) []
        ((unaryValues (ys.map (fun y => neighborhoodCount y radius xs))).reverse++out)) t ∧
      t  ≤  1+ys.length*(200*(xs.length+1)*(B+radius+1)) := by
  induction ys generalizing out with
  | nil =>
    refine ⟨1,?_,by simp⟩
    simpa [unaryValues,encodeBitList] using
      (WhileExecution.empty (robustStore 0 radius 0 [] (unaryValues xs) [] out) (by rfl))
  | cons y ys ih =>
    obtain ⟨tb,hb,hbt⟩ := robustBody_executes g y radius xs B
      (hys y (List.mem_cons_self)) hxs (unaryValues ys) out
    obtain ⟨tt,ht,htt⟩ := ih (fun z hz => hys z (List.mem_cons_of_mem _ hz))
      ((true::pairBits (List.replicate (neighborhoodCount y radius xs) true) []).reverse++out)
    have hpop : Function.update (robustStore 0 radius 0 [] (unaryValues xs) (unaryValues (y::ys)) out)
        (14 : Fin 16) (pairBits (List.replicate y true) (unaryValues ys)) =
        robustStore 0 radius 0 [] (unaryValues xs) (pairBits (List.replicate y true) (unaryValues ys)) out := by
      funext i; fin_cases i <;> rfl
    have hw := WhileExecution.one
      (s := robustStore 0 radius 0 [] (unaryValues xs) (unaryValues (y::ys)) out)
      (rest := pairBits (List.replicate y true) (unaryValues ys)) (by rfl) (by rw [hpop]; exact hb) ht
    refine ⟨2+tb+tt,?_,?_⟩
    · convert hw using 1
      · simp only [List.map_cons,unaryValues_reverse_cons,List.append_assoc]
      · omega
    · simp only [List.length_cons]
      nlinarith

/-- Fixed, oracle-free literal code computes all canonical neighborhood scores
with a quadratic scan bound and a completely clean work area. -/
theorem robustScores_executes (g : BitString → ℕ) (xs : List ℕ) (radius B : ℕ)
    (hxs : ∀ x ∈ xs, x ≤ B) :
    ∃ t, robustScores.Executes g
      (robustStore 0 radius 0 [] (unaryValues xs) (unaryValues xs) [])
      (robustStore 0 radius 0 [] (unaryValues xs)
        (unaryValues (xs.map (fun y => neighborhoodCount y radius xs))) []) t ∧
      t  ≤  500*(xs.length+1)^2*(B+radius+1)+20 := by
  let scores := xs.map (fun y => neighborhoodCount y radius xs)
  obtain ⟨tl,hl,hbl⟩ := robustScores_execution g xs xs radius B hxs hxs []
  simp only [List.append_nil] at hl
  have hloop := whilePop_executes _ _ _ _ hl
  have hr : (reverseOn (15 : Fin 16) 14 (by decide)).Executes g
      (robustStore 0 radius 0 [] (unaryValues xs) [] (unaryValues scores).reverse)
      (robustStore 0 radius 0 [] (unaryValues xs) (unaryValues scores) [])
      (2*(unaryValues scores).length+1) := by
    convert reverseOn_executes g (15 : Fin 16) 14 (by decide)
      (robustStore 0 radius 0 [] (unaryValues xs) [] (unaryValues scores).reverse) using 1
    · funext i; fin_cases i <;> simp [robustStore]
    · simp [robustStore]
  refine ⟨_,seq_executes _ _ g hloop hr,?_⟩
  have hlen : (unaryValues scores).length ≤ 2*xs.length*(xs.length+1) := by
    have hh := unaryValues_length_bound scores xs.length (by
      intro score hscore
      obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hscore
      exact neighborhoodCount_le y radius xs)
    simpa [scores] using hh
  nlinarith

end HiddenCircuits.Approximation.SelfReduction.Runtime
