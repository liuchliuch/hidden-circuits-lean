import HiddenCircuits.Complexity.GraphVerifier.TwoParse
import HiddenCircuits.Complexity.GraphVerifier.UnaryHeader
import HiddenCircuits.Complexity.GraphVerifier.LengthCompare

/-! Actual restored header scans and fixed certificate-length validation. -/
namespace HiddenCircuits.Complexity.GraphVerifier.Runtime
open OracleBlock

noncomputable def headerOn {k : ℕ} (φ : Fin 4 ↪ Fin (k+1)) : OracleBlock k := rename UnaryHeader.block φ

theorem headerOn_executes {k : ℕ} (φ : Fin 4 ↪ Fin (k+1)) (g : BitString → ℕ)
    (s : Store k) (xs : BitString) (hs : s∘φ=UnaryHeader.store xs [] [] []) :
    (headerOn φ).Executes g s
      (Function.update (Function.update s (φ 1) (List.replicate xs.length true)) (φ 3) [xs.all id])
      (5*xs.length+3) := by
  apply rename_executes_to UnaryHeader.block φ g (UnaryHeader.block_executes g xs) hs
  · have he : (Function.update (Function.update s (φ 1) (List.replicate xs.length true)) (φ 3) [xs.all id])∘φ=
        Function.update (Function.update (s∘φ) 1 (List.replicate xs.length true)) 3 [xs.all id] := by
      funext i
      simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i;fin_cases i <;> rfl
  · intro j hj
    rw [Function.update_of_ne (hj 3).symm,Function.update_of_ne (hj 1).symm]

 theorem headerOn_queryFree {k : ℕ} (φ : Fin 4 ↪ Fin (k+1)) : (headerOn φ).QueryFree :=
  rename_queryFree _ _ UnaryHeader.block_queryFree

def headerNEmbedding : Fin 4 ↪ Fin 15 where
  toFun i := if i.val=0 then 6 else if i.val=1 then 8 else if i.val=2 then 5 else 9
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
 def headerXEmbedding : Fin 4 ↪ Fin 15 where
  toFun i := if i.val=0 then 1 else if i.val=1 then 10 else if i.val=2 then 5 else 11
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
 def headerWEmbedding : Fin 4 ↪ Fin 15 where
  toFun i := if i.val=0 then 0 else if i.val=1 then 12 else if i.val=2 then 5 else 13
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
 def lengthsEmbedding : Fin 3 ↪ Fin 15 where
  toFun i := if i.val=0 then 10 else if i.val=1 then 12 else 14
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

noncomputable def headerStageBlock : OracleBlock 14 :=
  seq (headerOn headerNEmbedding) (seq (headerOn headerXEmbedding)
    (seq (headerOn headerWEmbedding) (rename lengthCompareBlock lengthsEmbedding)))

def prepStore (old : Store 7) (nClock nFlag xClock xFlag wClock wFlag lengthFlag : BitString) : Store 14 := fun i =>
  if h:i.val<8 then old ⟨i.val,h⟩ else if i.val=8 then nClock else if i.val=9 then nFlag
  else if i.val=10 then xClock else if i.val=11 then xFlag else if i.val=12 then wClock
  else if i.val=13 then wFlag else lengthFlag

/-- All scans are real finite blocks; the original witness, matrix and header remain available. -/
theorem headerStage_executes (g : BitString → ℕ) (xs : BitString) :
    ∃ a b cost, headerStageBlock.Executes g
      (prepStore (twoParseResult xs) [] [] [] [] [] [] [])
      (prepStore (twoParseResult xs) (List.replicate (parse (parse xs).left).left.length true)
        [(parse (parse xs).left).left.all id] a [(parse xs).left.all id] b [(parse xs).right.all id]
        [decide ((parse xs).left.length=(parse xs).right.length)]) cost ∧ cost ≤ 17*xs.length+18 := by
  let x := (parse xs).left
  let w := (parse xs).right
  let h := (parse x).left
  let old := twoParseResult xs
  let s₀ := prepStore old [] [] [] [] [] [] []
  let s₁ := prepStore old (List.replicate h.length true) [h.all id] [] [] [] [] []
  let s₂ := prepStore old (List.replicate h.length true) [h.all id] (List.replicate x.length true) [x.all id] [] [] []
  let s₃ := prepStore old (List.replicate h.length true) [h.all id] (List.replicate x.length true) [x.all id]
    (List.replicate w.length true) [w.all id] []
  have hn : (headerOn headerNEmbedding).Executes g s₀ s₁ (5*h.length+3) := by
    have hh := headerOn_executes headerNEmbedding g s₀ h (by funext i;fin_cases i <;> rfl)
    convert hh using 1
    funext i;fin_cases i <;> simp [s₀,s₁,prepStore,headerNEmbedding]
  have hx : (headerOn headerXEmbedding).Executes g s₁ s₂ (5*x.length+3) := by
    have hh := headerOn_executes headerXEmbedding g s₁ x (by funext i;fin_cases i <;> rfl)
    convert hh using 1
    funext i;fin_cases i <;> simp [s₁,s₂,prepStore,headerXEmbedding]
  have hw : (headerOn headerWEmbedding).Executes g s₂ s₃ (5*w.length+3) := by
    have hh := headerOn_executes headerWEmbedding g s₂ w (by funext i;fin_cases i <;> rfl)
    convert hh using 1
    funext i;fin_cases i <;> simp [s₂,s₃,prepStore,headerWEmbedding]
  obtain ⟨a,b,c,hc,hcb⟩ := lengthCompare_executes g (List.replicate x.length true) (List.replicate w.length true) []
  let out := prepStore old (List.replicate h.length true) [h.all id] a [x.all id] b [w.all id]
    [decide (x.length=w.length)]
  have hl : (rename lengthCompareBlock lengthsEmbedding).Executes g s₃ out c := by
    apply rename_executes_to lengthCompareBlock lengthsEmbedding g hc
    · funext i;fin_cases i <;> rfl
    · simp only [List.length_replicate]
      funext i;fin_cases i <;> rfl
    · intro j hj
      fin_cases j
      all_goals first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) | exact False.elim (hj 2 rfl)
  refine ⟨a,b,(5*h.length+3)+((5*x.length+3)+((5*w.length+3)+c+2)+2)+2,?_,?_⟩
  · exact seq_executes _ _ g hn (seq_executes _ _ g hx (seq_executes _ _ g hw hl))
  · have hxl := (parse_lengths xs).1
    have hwl := (parse_lengths xs).2
    have hhl := (parse_lengths x).1
    simp only [List.length_replicate] at hcb
    dsimp [h,x,w] at *
    omega

 theorem headerStage_queryFree : headerStageBlock.QueryFree :=
  seq_queryFree _ _ (headerOn_queryFree _) (seq_queryFree _ _ (headerOn_queryFree _)
    (seq_queryFree _ _ (headerOn_queryFree _) (rename_queryFree _ _ lengthCompare_queryFree)))

end HiddenCircuits.Complexity.GraphVerifier.Runtime
