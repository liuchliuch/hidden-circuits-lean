import HiddenCircuits.Complexity.PortLiteralEmitter
import HiddenCircuits.Complexity.RuleLiteralEmitter

/-! Actual output-literal generation for a local transition clause: compute the
next-row cell address, evaluate the fixed-boundary rule table, and serialize. -/
namespace HiddenCircuits.Complexity.OutputLiteralEmitter
open OracleBlock TM2BooleanEncoding Polynomial

abbrev Family (M : Turing.FinTM2) := Control M ⊕ Symbols M

def familyCell (M : Turing.FinTM2) (j r : ℕ) : Family M → Cell M (j+r+1)
  | .inl q => .inl q
  | .inr ⟨k,s⟩ => .inr ⟨k,(⟨j,by omega⟩,s)⟩

noncomputable def familyPort (M : Turing.FinTM2) : Family M → Port M
  | .inl q => .inl q
  | .inr ⟨k,s⟩ => .inr ⟨k,(.inr (0,0),s)⟩

lemma familyPort_address (M : Turing.FinTM2) (j r : ℕ) (f : Family M) :
    portAddress M (j+r+1) j (familyPort M f) = (cellEnumeration M (j+r+1) (familyCell M j r f)).val := by
  rw [portAddress_correct]
  congr 2
  cases f with
  | inl q => rfl
  | inr ks =>
    rcases ks with ⟨k,s⟩
    simp [familyPort,familyCell,portCell,portPosition,show j<j+r+1 by omega]

noncomputable def table (M : Turing.FinTM2) (f : Family M) (pattern : Port M → Bool)
    (j r : Fin (2*inspectionConstant M+1)) : Bool :=
  match f with
  | .inl q => controlRuleTable M (cappedPosition M (j.val+r.val+1)) q pattern
  | .inr ⟨k,s⟩ => stackRuleTable M j r k s pattern

lemma table_correct (M : Turing.FinTM2) (f : Family M) (pattern : Port M → Bool) (j r : ℕ) :
    table M f pattern (cappedPosition M j) (cappedPosition M r) =
      directRule M (j+r+1) (familyCell M j r f) pattern := by
  cases f with
  | inl q =>
    rw [familyCell,controlRuleTable_correct]
    unfold table
    have hc : cappedPosition M ((cappedPosition M j).val+(cappedPosition M r).val+1) =
        cappedPosition M (j+r+1) := by
      apply Fin.ext
      exact (cap_sum_succ (inspectionConstant M) j r).symm
    rw [hc]
  | inr ks =>
    rcases ks with ⟨k,s⟩
    rw [familyCell,stackRuleTable_correct]
    simpa [table] using congrArg (fun rr => stackRuleTable M (cappedPosition M j) (cappedPosition M rr) k s pattern)
      (show r=j+r+1-j-1 by omega)

noncomputable def ruleProgram (M : Turing.FinTM2) (f : Family M) (pattern : Port M → Bool) : OracleBlock 6 :=
  branchLength 0 (2*inspectionConstant M) (fun j => branchLength 5 (2*inspectionConstant M)
    (fun r => CNFEmitter.literal 2 6 (table M f pattern j r)))

theorem ruleProgram_executes (g : BitString → ℕ) (M : Turing.FinTM2) (f : Family M)
    (pattern : Port M → Bool) (j r base index : ℕ) (stream : BitString) :
    ∃ cost, (ruleProgram M f pattern).Executes g (PortLiteralEmitter.state j base index 0 0 r stream)
      (PortLiteralEmitter.state j base 0 0 0 r
        ((serializedLiteral index (directRule M (j+r+1) (familyCell M j r f) pattern)).reverse++stream)) cost ∧
      cost ≤ 27*index+20*inspectionConstant M+47 := by
  let s := PortLiteralEmitter.state j base index 0 0 r stream
  let cj := cappedLength (2*inspectionConstant M) (s 0)
  let cr := cappedLength (2*inspectionConstant M) (s 5)
  let sign := table M f pattern cj cr
  let t := PortLiteralEmitter.state j base 0 0 0 r ((serializedLiteral index sign).reverse++stream)
  have hl : (CNFEmitter.literal (2 : Fin 7) 6 sign).Executes g s t (27*index+43) := by
    have h := CNFEmitter.literal_executes g (2 : Fin 7) 6 (by decide) sign s
    convert h using 1
    · funext i;fin_cases i <;> simp [s,t,PortLiteralEmitter.state]
    · simp [s,PortLiteralEmitter.state]
  obtain ⟨rc,hr,hrb⟩ := branchLength_executes g (5 : Fin 7) (2*inspectionConstant M)
    (fun r => CNFEmitter.literal 2 6 (table M f pattern cj r)) s t _ hl
  obtain ⟨lc,he,hlb⟩ := branchLength_executes g (0 : Fin 7) (2*inspectionConstant M)
    (fun j => branchLength 5 (2*inspectionConstant M) (fun r => CNFEmitter.literal 2 6 (table M f pattern j r))) s t _ hr
  have hs : sign = directRule M (j+r+1) (familyCell M j r f) pattern := by
    have hj : cj=cappedPosition M j := by apply Fin.ext;simp [cj,s,PortLiteralEmitter.state,cappedLength,cappedPosition,Nat.min_comm]
    have hr : cr=cappedPosition M r := by apply Fin.ext;simp [cr,s,PortLiteralEmitter.state,cappedLength,cappedPosition,Nat.min_comm]
    dsimp only [sign];rw [hj,hr,table_correct]
  refine ⟨27*index+43+rc+lc,?_,by omega⟩
  simpa only [t,hs] using he

noncomputable def program (M : Turing.FinTM2) (f : Family M) (pattern : Port M → Bool) : OracleBlock 6 :=
  seq (PortLiteralEmitter.indexProgram M (familyPort M f)) (ruleProgram M f pattern)

noncomputable def time (M : Turing.FinTM2) (f : Family M) : Polynomial ℕ :=
  PortLiteralEmitter.time M (familyPort M f)+C (20*inspectionConstant M+4)

theorem program_executes (g : BitString → ℕ) (M : Turing.FinTM2) (f : Family M)
    (pattern : Port M → Bool) (j r base : ℕ) (stream : BitString) :
    ∃ cost, (program M f pattern).Executes g (PortLiteralEmitter.state j base 0 0 0 r stream)
      (PortLiteralEmitter.state j base 0 0 0 r
        ((serializedLiteral (base+(cellEnumeration M (j+r+1) (familyCell M j r f)).val)
          (directRule M (j+r+1) (familyCell M j r f) pattern)).reverse++stream)) cost ∧
      cost ≤ (time M f).eval (j+r+base) := by
  obtain ⟨ci,hi,hbi⟩ := PortLiteralEmitter.indexProgram_executes g M (familyPort M f) j r base stream
  obtain ⟨cr,hr,hbr⟩ := ruleProgram_executes g M f pattern j r base (base+portAddress M (j+r+1) j (familyPort M f)) stream
  refine ⟨ci+cr+2,?_,?_⟩
  · simpa only [familyPort_address] using seq_executes _ _ g hi hr
  · have hm := polynomial_nat_eval_mono (PortIndexEmitter.time M (familyPort M f)) (show j+base≤j+r+base by omega)
    dsimp only at hm
    have hx := PortLiteralEmitter.index_bound M (familyPort M f) j r base
    simp only [time,PortLiteralEmitter.time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,
      Polynomial.eval_C,Polynomial.eval_one,Polynomial.eval_ofNat]
    omega

lemma program_queryFree (M : Turing.FinTM2) (f : Family M) (pattern : Port M → Bool) : (program M f pattern).QueryFree :=
  seq_queryFree _ _ (rename_queryFree _ _ (PortIndexEmitter.program_queryFree _ _))
    (branchLength_queryFree _ _ _ (fun _ => branchLength_queryFree _ _ _ (fun _ => CNFEmitter.literal_queryFree _ _ _)))

end HiddenCircuits.Complexity.OutputLiteralEmitter
