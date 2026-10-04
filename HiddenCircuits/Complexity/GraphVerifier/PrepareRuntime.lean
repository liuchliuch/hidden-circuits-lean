import HiddenCircuits.Complexity.GraphVerifier.HeaderStage

/-! Full actual certificate/graph parsing and restored unary-clock preparation. -/
namespace HiddenCircuits.Complexity.GraphVerifier.Runtime
open OracleBlock

def prepareEmbedding : Fin 8 ↪ Fin 15 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h; exact Fin.ext (congrArg (fun z : Fin 15 => z.val) h)

noncomputable def prepareBlock : OracleBlock 14 := seq (rename twoParseBlock prepareEmbedding) headerStageBlock

def preparedStore (xs a b : BitString) : Store 14 :=
  prepStore (twoParseResult xs) (List.replicate (parse (parse xs).left).left.length true)
    [(parse (parse xs).left).left.all id] a [(parse xs).left.all id] b [(parse xs).right.all id]
    [decide ((parse xs).left.length=(parse xs).right.length)]

/-- All parsing, clock creation and header flags are actual bit instructions, on arbitrary raw strings. -/
theorem prepare_executes (g : BitString → ℕ) (xs : BitString) :
    ∃ a b cost, prepareBlock.Executes g (Function.update (fun _ : Fin 15 => ([]:BitString)) 0 xs)
      (preparedStore xs a b) cost ∧ cost ≤ 28*xs.length+34 := by
  have hp : (rename twoParseBlock prepareEmbedding).Executes g
      (Function.update (fun _ : Fin 15 => ([]:BitString)) 0 xs)
      (prepStore (twoParseResult xs) [] [] [] [] [] [] []) (twoParseCost xs) := by
    apply rename_executes_to twoParseBlock prepareEmbedding g (twoParse_executes g xs)
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro j hj
      fin_cases j
      all_goals first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) |
        exact False.elim (hj 2 rfl) | exact False.elim (hj 3 rfl) | exact False.elim (hj 4 rfl) |
        exact False.elim (hj 5 rfl) | exact False.elim (hj 6 rfl) | exact False.elim (hj 7 rfl)
  obtain ⟨a,b,c,hc,hbound⟩ := headerStage_executes g xs
  refine ⟨a,b,twoParseCost xs+c+2,seq_executes _ _ g hp hc,?_⟩
  have hh := twoParse_cost_bound xs
  omega

 theorem prepare_queryFree : prepareBlock.QueryFree :=
  seq_queryFree _ _ (rename_queryFree _ _ twoParse_queryFree) headerStage_queryFree

/-- Exact semantic outputs needed by the remaining graph scan. -/
theorem preparedStore_ports (xs a b : BitString) :
    preparedStore xs a b 0=(parse xs).right ∧
    preparedStore xs a b 4=(parse (parse xs).left).right ∧
    preparedStore xs a b 8=List.replicate (parse (parse xs).left).left.length true ∧
    preparedStore xs a b 3=[(parse xs).ok] ∧
    preparedStore xs a b 7=[(parse (parse xs).left).ok] ∧
    preparedStore xs a b 9=[(parse (parse xs).left).left.all id] ∧
    preparedStore xs a b 14=[decide ((parse xs).left.length=(parse xs).right.length)] := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end HiddenCircuits.Complexity.GraphVerifier.Runtime
