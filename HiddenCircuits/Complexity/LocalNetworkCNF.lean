import HiddenCircuits.Complexity.TruthTableCNF
import HiddenCircuits.Complexity.UniqueTableau

/-! Polynomial tableau CNFs for fixed-width local Boolean transitions. The local
width is explicit: the exponential truth-table factor is 2^width, not exponential
in the number of cells or the running time. -/
namespace HiddenCircuits.Complexity
attribute [local instance] Classical.propDecidable
open BoolCircuit

structure LocalNetwork (cells width : ℕ) where
  ports : Fin cells → Fin width → Fin cells
  rule : Fin cells → (Fin width → Bool) → Bool

namespace LocalNetwork
variable {n r : ℕ} (N : LocalNetwork n r)

def step (w : Fin n → Bool) : Fin n → Bool := fun v => N.rule v (fun k => w (N.ports v k))
abbrev Variable (t : ℕ) := Fin (t+1) × Fin n

noncomputable def localClauses (t : ℕ) (i : Fin t) (v : Fin n) : RawCNF (Variable (n := n) t) :=
  TruthTableCNF.clauses (fun k => (i.castSucc,N.ports v k))
    (fun _ : Fin 1 => (i.succ,v)) (fun a _ => N.rule v a)

noncomputable def clauses (t : ℕ) : RawCNF (Variable (n := n) t) :=
  (Finset.univ : Finset (Fin t × Fin n)).toList.flatMap
    (fun iv => N.localClauses t iv.1 iv.2)

theorem localClauses_correct (t : ℕ) (i : Fin t) (v : Fin n)
    (w : Variable (n := n) t → Bool) :
    RawSatisfies (N.localClauses t i v) w ↔
      w (i.succ,v) = N.step (fun x => w (i.castSucc,x)) v := by
  rw [localClauses,TruthTableCNF.clauses_correct]
  simp only [step,forall_const]

theorem clauses_correct (t : ℕ) (w : Variable (n := n) t → Bool) :
    RawSatisfies (N.clauses t) w ↔
      ∀ i : Fin t, ∀ v : Fin n, w (i.succ,v) = N.step (fun x => w (i.castSucc,x)) v := by
  classical
  constructor
  · intro h i v
    apply (N.localClauses_correct t i v w).mp
    intro c hc
    apply h c
    exact List.mem_flatMap.mpr ⟨(i,v),by simp,hc⟩
  · intro h c hc
    obtain ⟨⟨i,v⟩,_,hc⟩ := List.mem_flatMap.mp hc
    exact (N.localClauses_correct t i v w).mpr (h i v) c hc

/-- The emitted update constraints have the exact expected size. -/
theorem clauses_length (t : ℕ) : (N.clauses t).length = t*n*2^r := by
  classical
  simp [clauses,localClauses,List.length_flatMap,TruthTableCNF.clauses_length]

def canonical (t : ℕ) (initial : Fin n → Bool) : Variable (n := n) t → Bool :=
  fun iv => (N.step^[iv.1.val] initial) iv.2

def initial (t : ℕ) (w : Variable (n := n) t → Bool) : Fin n → Bool := fun v => w (0,v)

theorem canonical_valid (t : ℕ) (input : Fin n → Bool) : RawSatisfies (N.clauses t) (N.canonical t input) := by
  rw [N.clauses_correct]
  intro i v
  change (N.step^[i.val+1] input) v = N.step (N.step^[i.val] input) v
  rw [Function.iterate_succ_apply']

/-- Satisfying assignments are uniquely determined by the first row. -/
theorem clauses_unique (t : ℕ) (w : Variable (n := n) t → Bool)
    (hw : RawSatisfies (N.clauses t) w) : w = N.canonical t (initial t w) := by
  let tab : Tableau N.step (initial t w) t :=
    ⟨fun i v => w (i,v),rfl,fun i => funext ((N.clauses_correct t w).mp hw i)⟩
  funext iv
  exact congrFun (tab.state_eq_iterate iv.1) iv.2

noncomputable def acceptingClauses (t : ℕ) (out : Fin n) : RawCNF (Variable (n := n) t) :=
  N.clauses t ++ [[((Fin.last t,out),true)]]

theorem acceptingClauses_correct (t : ℕ) (out : Fin n) (w : Variable (n := n) t → Bool) :
    RawSatisfies (N.acceptingClauses t out) w ↔
      RawSatisfies (N.clauses t) w ∧ w (Fin.last t,out) = true := by
  rw [acceptingClauses,rawSatisfies_append]
  simp [RawSatisfies]

@[simp] theorem acceptingClauses_length (t : ℕ) (out : Fin n) :
    (N.acceptingClauses t out).length = t*n*2^r+1 := by
  simp [acceptingClauses,N.clauses_length]

noncomputable def acceptingEquiv (t : ℕ) (out : Fin n) :
    {input : Fin n → Bool // (N.step^[t] input) out = true} ≃
    {w : Variable (n := n) t → Bool // RawSatisfies (N.acceptingClauses t out) w} where
  toFun w := ⟨N.canonical t w.val,(N.acceptingClauses_correct t out _).mpr
    ⟨N.canonical_valid t w.val,w.property⟩⟩
  invFun w := ⟨initial t w.val,by
    have h := (N.acceptingClauses_correct t out w.val).mp w.property
    have he := congrFun (N.clauses_unique t w.val h.1) (Fin.last t,out)
    exact he.symm.trans h.2⟩
  left_inv w := rfl
  right_inv w := Subtype.ext (N.clauses_unique t w.val
    ((N.acceptingClauses_correct t out w.val).mp w.property).1).symm

/-- Exact counting, rather than satisfiability alone. -/
theorem accepting_count (t : ℕ) (out : Fin n) :
    Nat.card {w : Variable (n := n) t → Bool // RawSatisfies (N.acceptingClauses t out) w} =
    Nat.card {input : Fin n → Bool // (N.step^[t] input) out = true} := by
  classical
  exact Nat.card_congr (N.acceptingEquiv t out).symm

end LocalNetwork
end HiddenCircuits.Complexity
