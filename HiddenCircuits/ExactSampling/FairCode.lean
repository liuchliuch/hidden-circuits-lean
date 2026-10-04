import HiddenCircuits.Complexity.OracleBlockNoQuery

/-!
# Finite fair-coin programs with unbounded execution

The syntax is finite. Every deterministic leaf is an actual finite binary-stack
program, and every random instruction reads exactly one fair bit. The only
unbounded operation is a while loop whose individual iterations are recorded in
`Runs`. Macro calls are charged their full underlying instruction execution.
This model extends the fixed-tape polynomial `RandomBitProgram`; it does not
pretend that exact non-dyadic output probabilities fit a bounded random tape.
-/
namespace HiddenCircuits.ExactSampling
open Complexity OracleBlock

inductive FairCode (k : ℕ)
  | block (B : OracleBlock k)
  | coin (stack : Fin (k+1))
  | seq (B C : FairCode k)
  | branchPop (stack : Fin (k+1)) (empty zero one : FairCode k)
  | whilePop (stack : Fin (k+1)) (zero one : FairCode k)

namespace FairCode
variable {k : ℕ}

/-- A structural query-free check on the fixed finite syntax. -/
def QueryFree : FairCode k → Prop
  | .block B => B.QueryFree
  | .coin _ => True
  | .seq B C => B.QueryFree ∧ C.QueryFree
  | .branchPop _ E B C => E.QueryFree ∧ B.QueryFree ∧ C.QueryFree
  | .whilePop _ B C => B.QueryFree ∧ C.QueryFree

/-- An explicit finite control-size bound. Deterministic blocks can be expanded
into their finite instruction tables; all remaining constructs add only fixed
control labels. The bound is independent of inputs and random traces. -/
def controlSize : FairCode k → ℕ
  | .block B => B.labelCount+1
  | .coin _ => 2
  | .seq B C => B.controlSize+C.controlSize+2
  | .branchPop _ E B C => E.controlSize+B.controlSize+C.controlSize+3
  | .whilePop _ B C => B.controlSize+C.controlSize+2

/-- Operational finite-prefix semantics. The random list consists exactly of
bits read by the coin instructions, in read order. No fairness, halting, or
runtime assertion is a field of the program; those must be proved separately. -/
inductive Runs : FairCode k → Store k → Store k → List Bool → ℕ → Prop
  | block {B : OracleBlock k} {s t : Store k} {c : ℕ}
      (h : B.Executes (fun _=>0) s t c) : Runs (.block B) s t [] c
  | coin (s : Store k) (stack : Fin (k+1)) (b : Bool) :
      Runs (.coin stack) s (Function.update s stack (b::s stack)) [b] 1
  | seq {B C : FairCode k} {s t u : Store k} {xs ys : List Bool} {a b : ℕ}
      (hB : Runs B s t xs a) (hC : Runs C t u ys b) :
      Runs (.seq B C) s u (xs++ys) (a+b+2)
  | branchEmpty {q : Fin (k+1)} {E B C : FairCode k} {s t : Store k} {xs : List Bool} {c : ℕ}
      (h : s q=[]) (run : Runs E s t xs c) : Runs (.branchPop q E B C) s t xs (c+2)
  | branchFalse {q : Fin (k+1)} {E B C : FairCode k} {s t : Store k} {rest xs : List Bool} {c : ℕ}
      (h : s q=false::rest) (run : Runs B (Function.update s q rest) t xs c) :
      Runs (.branchPop q E B C) s t xs (c+2)
  | branchTrue {q : Fin (k+1)} {E B C : FairCode k} {s t : Store k} {rest xs : List Bool} {c : ℕ}
      (h : s q=true::rest) (run : Runs C (Function.update s q rest) t xs c) :
      Runs (.branchPop q E B C) s t xs (c+2)
  | loopEmpty {q : Fin (k+1)} {B C : FairCode k} (s : Store k) (h : s q=[]) :
      Runs (.whilePop q B C) s s [] 1
  | loopFalse {q : Fin (k+1)} {B C : FairCode k} {s t u : Store k}
      {rest xs ys : List Bool} {a b : ℕ} (h : s q=false::rest)
      (head : Runs B (Function.update s q rest) t xs a)
      (tail : Runs (.whilePop q B C) t u ys b) :
      Runs (.whilePop q B C) s u (xs++ys) (1+a+1+b)
  | loopTrue {q : Fin (k+1)} {B C : FairCode k} {s t u : Store k}
      {rest xs ys : List Bool} {a b : ℕ} (h : s q=true::rest)
      (head : Runs C (Function.update s q rest) t xs a)
      (tail : Runs (.whilePop q B C) t u ys b) :
      Runs (.whilePop q B C) s u (xs++ys) (1+a+1+b)

/-- Random bits are always charged individually, including all rejected trials. -/
 theorem Runs.bits_le_cost {P : FairCode k} {s t : Store k} {xs : List Bool} {c : ℕ}
    (h : Runs P s t xs c) : xs.length≤c := by
  induction h <;> simp only [List.length_nil,List.length_singleton,List.length_append] at * <;> omega

/-- Finite deterministic syntax does not bound the number of loop iterations. -/
 theorem controlSize_positive (P : FairCode k) : 0<P.controlSize := by cases P <;> simp [controlSize] <;> omega

end FairCode
end HiddenCircuits.ExactSampling
