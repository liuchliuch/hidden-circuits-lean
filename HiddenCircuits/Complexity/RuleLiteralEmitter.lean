import HiddenCircuits.Complexity.TM2FiniteRuleTable
import HiddenCircuits.Complexity.CNFEmitter
import HiddenCircuits.Complexity.OracleCapBranch

/-! Actual finite code evaluates each TM2 local rule via its proved fixed-size
boundary table, then emits the exact result literal. The table is fixed with the
verifier; all input-dependent boundary selection uses verified bit instructions. -/
namespace HiddenCircuits.Complexity.RuleLiteralEmitter
open OracleBlock TM2BooleanEncoding
variable {k : ℕ}

lemma cappedLength_eq (M : Turing.FinTM2) (s : BitString) :
    cappedLength (2*inspectionConstant M) s = cappedPosition M s.length := by
  apply Fin.ext;simp [cappedLength,cappedPosition,Nat.min_comm]

noncomputable def controlLiteral (M : Turing.FinTM2) (q : Control M) (pattern : Port M → Bool)
    (height counter output : Fin (k+1)) : OracleBlock k :=
  branchLength height (2*inspectionConstant M)
    (fun h => CNFEmitter.literal counter output (controlRuleTable M h q pattern))

theorem controlLiteral_executes (g : BitString → ℕ) (M : Turing.FinTM2) (q : Control M)
    (pattern : Port M → Bool) (height counter output : Fin (k+1)) (hne : counter ≠ output) (s : Store k) :
    ∃ cost, (controlLiteral M q pattern height counter output).Executes g s
      (Function.update (Function.update s counter []) output
        ((serializedLiteral (s counter).length
          (directRule M (s height).length (Sum.inl q) pattern)).reverse++s output)) cost ∧
      cost ≤ 27*(s counter).length+10*inspectionConstant M+45 := by
  have hl := CNFEmitter.literal_executes g counter output hne
    (controlRuleTable M (cappedLength (2*inspectionConstant M) (s height)) q pattern) s
  obtain ⟨overhead,he,hbound⟩ := branchLength_executes g height (2*inspectionConstant M)
    (fun h => CNFEmitter.literal counter output (controlRuleTable M h q pattern)) s _ _ hl
  refine ⟨27*(s counter).length+43+overhead,?_,by omega⟩
  simpa only [cappedLength_eq,← controlRuleTable_correct] using he

noncomputable def stackLiteral (M : Turing.FinTM2) (stack : M.K) (symbol : Option (Symbol M stack))
    (pattern : Port M → Bool) (left right counter output : Fin (k+1)) : OracleBlock k :=
  branchLength left (2*inspectionConstant M) (fun j =>
    branchLength right (2*inspectionConstant M) (fun r =>
      CNFEmitter.literal counter output (stackRuleTable M j r stack symbol pattern)))

theorem stackLiteral_executes (g : BitString → ℕ) (M : Turing.FinTM2) (stack : M.K)
    (symbol : Option (Symbol M stack)) (pattern : Port M → Bool)
    (left right counter output : Fin (k+1)) (hne : counter ≠ output) (s : Store k) :
    let H := (s left).length+(s right).length+1
    let i : Fin H := ⟨(s left).length,by omega⟩
    ∃ cost, (stackLiteral M stack symbol pattern left right counter output).Executes g s
      (Function.update (Function.update s counter []) output
        ((serializedLiteral (s counter).length (directRule M H (Sum.inr ⟨stack,(i,symbol)⟩) pattern)).reverse++s output)) cost ∧
      cost ≤ 27*(s counter).length+20*inspectionConstant M+47 := by
  dsimp only
  let j := cappedLength (2*inspectionConstant M) (s left)
  let r := cappedLength (2*inspectionConstant M) (s right)
  let sign := stackRuleTable M j r stack symbol pattern
  let t := Function.update (Function.update s counter []) output ((serializedLiteral (s counter).length sign).reverse++s output)
  have hl : (CNFEmitter.literal counter output sign).Executes g s t (27*(s counter).length+43) :=
    CNFEmitter.literal_executes g counter output hne sign s
  obtain ⟨oright,hr,hbr⟩ := branchLength_executes g right (2*inspectionConstant M)
    (fun r => CNFEmitter.literal counter output (stackRuleTable M j r stack symbol pattern)) s t _ hl
  obtain ⟨oleft,he,hbl⟩ := branchLength_executes g left (2*inspectionConstant M)
    (fun j => branchLength right (2*inspectionConstant M)
      (fun r => CNFEmitter.literal counter output (stackRuleTable M j r stack symbol pattern))) s t _ hr
  have hsign : sign = directRule M ((s left).length+(s right).length+1)
      (Sum.inr ⟨stack,(⟨(s left).length,by omega⟩,symbol)⟩) pattern := by
    rw [stackRuleTable_correct]
    simp only [show (s left).length+(s right).length+1-(s left).length-1=(s right).length by omega]
    simp [sign,j,r,cappedLength_eq]
  refine ⟨27*(s counter).length+43+oright+oleft,?_,by omega⟩
  simpa only [t,hsign] using he

lemma controlLiteral_queryFree (M : Turing.FinTM2) (q : Control M) (pattern : Port M → Bool)
    (height counter output : Fin (k+1)) : (controlLiteral M q pattern height counter output).QueryFree :=
  branchLength_queryFree _ _ _ (fun _ => CNFEmitter.literal_queryFree _ _ _)

lemma stackLiteral_queryFree (M : Turing.FinTM2) (stack : M.K) (symbol : Option (Symbol M stack))
    (pattern : Port M → Bool) (left right counter output : Fin (k+1)) :
    (stackLiteral M stack symbol pattern left right counter output).QueryFree :=
  branchLength_queryFree _ _ _ (fun _ => branchLength_queryFree _ _ _ (fun _ => CNFEmitter.literal_queryFree _ _ _))

end HiddenCircuits.Complexity.RuleLiteralEmitter
