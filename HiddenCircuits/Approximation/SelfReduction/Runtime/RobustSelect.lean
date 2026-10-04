import HiddenCircuits.Approximation.SelfReduction.Runtime.RobustMaximum
import HiddenCircuits.Approximation.SelfReduction.Runtime.ListLookup

/-! A complete actual finite machine for confidence boosting a vector of bounded
natural estimates. It returns the selected count, with all scratch cleared. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

def robustPickEmbedding : Fin 5 ↪ Fin 16 where
  toFun i := if i.val=0 then 13 else if i.val=1 then 1 else if i.val=2 then 0
    else if i.val=3 then 3 else 4
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

noncomputable def robustPick : OracleBlock 15 :=
  seq (clear 0) (seq (clear 2) (rename listLookup robustPickEmbedding))
noncomputable def robustSelect : OracleBlock 15 := seq robustSelectScores robustPick

 theorem robustPick_executes (g : BitString → ℕ) (n best pos : ℕ) (q : Fin (n+1) → ℕ) (j : Fin (n+1)) :
    ∃ t, robustPick.Executes g
      (robustStore best j.val pos [] (unaryValues (List.ofFn q)) [] [])
      (robustStore (q j) 0 0 [] [] [] []) t ∧
      t ≤ best+pos+7*(unaryValues (List.ofFn q)).length+21 := by
  have h1 : (clear (0 : Fin 16)).Executes g
      (robustStore best j.val pos [] (unaryValues (List.ofFn q)) [] [])
      (robustStore 0 j.val pos [] (unaryValues (List.ofFn q)) [] []) (best+1) := by
    convert clear_executes g (0 : Fin 16)
      (robustStore best j.val pos [] (unaryValues (List.ofFn q)) [] []) using 1
    · funext i; fin_cases i <;> rfl
    · simp [robustStore]
  have h2 : (clear (2 : Fin 16)).Executes g
      (robustStore 0 j.val pos [] (unaryValues (List.ofFn q)) [] [])
      (robustStore 0 j.val 0 [] (unaryValues (List.ofFn q)) [] []) (pos+1) := by
    convert clear_executes g (2 : Fin 16)
      (robustStore 0 j.val pos [] (unaryValues (List.ofFn q)) [] []) using 1
    · funext i; fin_cases i <;> rfl
    · simp [robustStore]
  let words := List.ofFn (fun i => List.replicate (q i) true)
  let j' : Fin words.length := ⟨j.val,by simpa [words] using j.isLt⟩
  obtain ⟨tl,hl,hbl⟩ := listLookup_index g words j'
  have hin : encodeBitList words=unaryValues (List.ofFn q) := by simp only [words,unaryValues,List.map_ofFn,Function.comp_def]
  have hout : words.get j'=List.replicate (q j) true := by
    simp only [words, List.get_eq_getElem, List.getElem_ofFn]
    rfl
  rw [hin] at hl hbl
  rw [hout] at hl
  have h3 : (rename listLookup robustPickEmbedding).Executes g
      (robustStore 0 j.val 0 [] (unaryValues (List.ofFn q)) [] [])
      (robustStore (q j) 0 0 [] [] [] []) tl := by
    apply rename_executes_to listLookup robustPickEmbedding g hl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
    · intro i hi; fin_cases i
      all_goals first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl)
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 h3),?_⟩
  omega

/-- Fixed finite confidence-booster implementation, with an explicit cubic
unary-data polynomial bound and exactly the analyzed selected count. -/
theorem robustSelect_executes (g : BitString → ℕ) (n radius B : ℕ) (q : Fin (n+1) → ℕ)
    (hq : ∀ i, q i ≤ B) :
    ∃ t, robustSelect.Executes g
      (robustStore 0 radius 0 [] (unaryValues (List.ofFn q)) [] [])
      (robustStore (q (chooseMax n (scoreVector n q radius))) 0 0 [] [] [] []) t ∧
      t ≤ 2000*(n+2)^2*(B+radius+1)+200 := by
  obtain ⟨ts,hs,hbs⟩ := robustSelectScores_executes g n radius B q hq
  obtain ⟨tp,hp,hbp⟩ := robustPick_executes g n
    (scoreVector n q radius (chooseMax n (scoreVector n q radius))) (n+1) q
    (chooseMax n (scoreVector n q radius))
  refine ⟨_,seq_executes _ _ g hs hp,?_⟩
  have hscore := scoreVector_le n q radius (chooseMax n (scoreVector n q radius))
  have hlen : (unaryValues (List.ofFn q)).length ≤ 2*(n+1)*(B+1) := by
    apply (unaryValues_length_bound _ B ?_).trans
    · simp
    · intro x hx; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx; exact hq i
  nlinarith

end HiddenCircuits.Approximation.SelfReduction.Runtime
