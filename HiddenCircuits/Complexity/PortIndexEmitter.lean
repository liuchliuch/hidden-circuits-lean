import HiddenCircuits.Complexity.TM2PortArithmetic
import HiddenCircuits.Complexity.UnaryIndex
import HiddenCircuits.Complexity.OracleCapBranch

/-! Uniform operational TM2 port addressing. Fixed finite boundary classes select
actual affine-index bit programs. Both the row base and position are restored;
only the result register changes, and the complete work store is accounted for. -/
namespace HiddenCircuits.Complexity.PortIndexEmitter
open OracleBlock TM2BooleanEncoding Polynomial

structure Parameters where
  remove : ℕ
  insert : ℕ
  scale : ℕ
  offset : ℕ

noncomputable def Parameters.time (P : Parameters) : Polynomial ℕ :=
  C (3*P.scale+13)*X+C ((3*P.scale+6)*P.insert+2*P.remove+3*P.offset+20)

def Parameters.value (P : Parameters) (position base : ℕ) : ℕ :=
  base+P.scale*(position-P.remove+P.insert)+P.offset

lemma build_cost_le (P : Parameters) (position base : ℕ) :
    5*base+5*position+(3*P.scale+3)*(position-P.remove+P.insert)+2*P.remove+3*P.insert+3*P.offset+20 ≤
      P.time.eval (position+base) := by
  simp only [Parameters.time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  have h := Nat.mul_le_mul_left (3*P.scale+3)
    (show position-P.remove+P.insert ≤ position+base+P.insert by omega)
  nlinarith

def state (position base result counter temporary right : ℕ) : Store 5 := fun i =>
  List.replicate (if i.val=0 then position else if i.val=1 then base else if i.val=2 then result
    else if i.val=3 then counter else if i.val=4 then temporary else right) true

noncomputable def build (P : Parameters) : OracleBlock 5 :=
  rename (UnaryIndex.build P.remove P.insert P.scale P.offset) (Fin.castAddEmb 1)

theorem build_executes (g : BitString → ℕ) (P : Parameters) (position base right : ℕ) :
    ∃ cost, (build P).Executes g (state position base 0 0 0 right)
      (state position base (P.value position base) 0 0 right) cost ∧ cost ≤ P.time.eval (position+base) := by
  obtain ⟨cost,hc,hb⟩ := UnaryIndex.build_executes g P.remove P.insert P.scale P.offset position base
  refine ⟨cost,?_,hb.trans (build_cost_le P position base)⟩
  apply rename_executes_to _ (Fin.castAddEmb 1) g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro j hj
    fin_cases j
    · exact (hj 0 rfl).elim
    · exact (hj 1 rfl).elim
    · exact (hj 2 rfl).elim
    · exact (hj 3 rfl).elim
    · exact (hj 4 rfl).elim
    · rfl

lemma build_queryFree (P : Parameters) : (build P).QueryFree := rename_queryFree _ _ (UnaryIndex.build_queryFree _ _ _ _)

noncomputable def validParameters (M : Turing.FinTM2) : Port M → Parameters
  | .inl q => ⟨0,0,0,controlIndex M q⟩
  | .inr ⟨k,(pos,symbol)⟩ => match pos with
    | .inl i => ⟨0,0,0,controlBits M+i.val*symbolBits M+symbolIndex M k symbol⟩
    | .inr (a,b) => ⟨a.val,b.val,symbolBits M,controlBits M+symbolIndex M k symbol⟩

noncomputable def dummyParameters (M : Turing.FinTM2) : Parameters :=
  ⟨0,0,0,controlIndex M (none,M.initialState)⟩

noncomputable def chosenParameters (M : Turing.FinTM2) (p : Port M)
    (j r : Fin (2*inspectionConstant M+1)) : Parameters :=
  match p with
  | .inl _ => validParameters M p
  | .inr ⟨_,(pos,_)⟩ => if portValidTable M j r pos then validParameters M p else dummyParameters M

theorem chosenParameters_value (M : Turing.FinTM2) (p : Port M) (j r base : ℕ) :
    (chosenParameters M p (cappedPosition M j) (cappedPosition M r)).value j base =
      base+portAddress M (j+r+1) j p := by
  cases p with
  | inl q => simp [chosenParameters,validParameters,Parameters.value,portAddress]
  | inr p =>
    rcases p with ⟨k,pos,symbol⟩
    rw [chosenParameters,portValidTable_correct]
    by_cases h : portPosition M j pos < j+r+1
    · simp only [h,decide_true,ite_true,portAddress,if_pos h]
      cases pos with
      | inl i => simp [validParameters,Parameters.value,portPosition,Nat.add_assoc]
      | inr ab => rcases ab with ⟨a,b⟩;simp [validParameters,Parameters.value,portPosition];ring
    · simp only [h,decide_false,ite_false,portAddress,if_neg h]
      simp [dummyParameters,Parameters.value]

lemma chosen_time_le (M : Turing.FinTM2) (p : Port M) (j r : Fin (2*inspectionConstant M+1)) (n : ℕ) :
    (chosenParameters M p j r).time.eval n ≤ (validParameters M p).time.eval n+(dummyParameters M).time.eval n := by
  cases p with
  | inl q => exact Nat.le_add_right _ _
  | inr p =>
    rcases p with ⟨k,pos,symbol⟩
    simp only [chosenParameters]
    split_ifs
    · exact Nat.le_add_right _ _
    · exact Nat.le_add_left _ _

noncomputable def program (M : Turing.FinTM2) (p : Port M) : OracleBlock 5 :=
  branchLength 0 (2*inspectionConstant M) (fun j =>
    branchLength 5 (2*inspectionConstant M) (fun r => build (chosenParameters M p j r)))

noncomputable def time (M : Turing.FinTM2) (p : Port M) : Polynomial ℕ :=
  (validParameters M p).time+(dummyParameters M).time+C (20*inspectionConstant M+4)

/-- The complete real program produces the actual CNF row-offset port index.
All input-dependent arithmetic is on bit stacks, with a linear polynomial bound. -/
theorem program_executes (g : BitString → ℕ) (M : Turing.FinTM2) (p : Port M) (j r base : ℕ) :
    ∃ cost, (program M p).Executes g (state j base 0 0 0 r)
      (state j base (base+portAddress M (j+r+1) j p) 0 0 r) cost ∧
      cost ≤ (time M p).eval (j+base) := by
  let s := state j base 0 0 0 r
  let cj := cappedLength (2*inspectionConstant M) (s 0)
  let cr := cappedLength (2*inspectionConstant M) (s 5)
  have hj : cj = cappedPosition M j := by apply Fin.ext;simp [cj,s,state,cappedLength,cappedPosition,Nat.min_comm]
  have hr : cr = cappedPosition M r := by apply Fin.ext;simp [cr,s,state,cappedLength,cappedPosition,Nat.min_comm]
  let P := chosenParameters M p cj cr
  obtain ⟨bodyCost,hbody,hb⟩ := build_executes g P j base r
  obtain ⟨rightCost,hinner,hri⟩ := branchLength_executes g (5 : Fin 6) (2*inspectionConstant M)
    (fun r => build (chosenParameters M p cj r)) s _ bodyCost hbody
  obtain ⟨leftCost,hwhole,hle⟩ := branchLength_executes g (0 : Fin 6) (2*inspectionConstant M)
    (fun j => branchLength 5 (2*inspectionConstant M) (fun r => build (chosenParameters M p j r))) s _ _ hinner
  have hv : P.value j base = base+portAddress M (j+r+1) j p := by
    dsimp only [P];rw [hj,hr,chosenParameters_value]
  refine ⟨bodyCost+rightCost+leftCost,?_,?_⟩
  · simpa only [hv] using hwhole
  · have hc := chosen_time_le M p cj cr (j+base)
    change bodyCost ≤ (chosenParameters M p cj cr).time.eval (j+base) at hb
    simp only [time,Polynomial.eval_add,Polynomial.eval_C]
    omega

lemma program_queryFree (M : Turing.FinTM2) (p : Port M) : (program M p).QueryFree :=
  branchLength_queryFree _ _ _ (fun _ => branchLength_queryFree _ _ _ (fun _ => build_queryFree _))

end HiddenCircuits.Complexity.PortIndexEmitter
