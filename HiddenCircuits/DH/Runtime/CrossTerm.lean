import HiddenCircuits.DH.Runtime.CoefficientModel
import HiddenCircuits.Complexity.BinaryArithmetic.StraightLine

/-! Literal finite bit-stack arithmetic for one true-twin summand. The index
factorials are inputs here; their actual producer is the existing factorial
block, and no arithmetic operation is treated as a unit-cost oracle. -/
namespace HiddenCircuits.DH.Runtime.CrossTerm
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic
open Complexity.BinaryArithmetic.RegisterMachine
open scoped BigOperators
set_option maxHeartbeats 1200000

/-- Registers 0..4 hold five factorials; 5 and 6 hold the two cached counts. -/
def registers (i j r A B : ℕ) : Fin 7→ℤ :=
  ![(i.factorial:ℤ),(j.factorial:ℤ),(r.factorial:ℤ),((i-r).factorial:ℤ),((j-r).factorial:ℤ),(A:ℤ),(B:ℤ)]

def code : List Instruction :=
  [⟨.multiply,0,0,1⟩,⟨.multiply,2,2,3⟩,⟨.multiply,2,2,4⟩,
   ⟨.divide,0,0,2⟩,⟨.multiply,5,5,6⟩,⟨.multiply,0,0,5⟩]

noncomputable def program : OracleBlock 15 := compile code

def denominator (i j r : ℕ) : ℕ := r.factorial*(i-r).factorial*(j-r).factorial

lemma denominator_pos (i j r : ℕ) : 0<denominator i j r := by unfold denominator;positivity

lemma quotient (i j r : ℕ) (hri : r ≤ i) (hrj : r ≤ j) :
    (i.factorial:ℤ)*j.factorial / ((r.factorial:ℤ)*(i-r).factorial*(j-r).factorial) =
      (i.choose r*j.choose r*r.factorial : ℕ) := by
  exact_mod_cast CoefficientModel.crossing_division i j r hri hrj

lemma divisor (i j r : ℕ) (hri : r ≤ i) (hrj : r ≤ j) :
    (r.factorial:ℤ)*(i-r).factorial*(j-r).factorial ∣ (i.factorial:ℤ)*j.factorial := by
  refine ⟨(i.choose r*j.choose r*r.factorial : ℕ),?_⟩
  have h := CoefficientModel.crossing_factorial i j r hri hrj
  have hc := congrArg (fun z : ℕ=>(z:ℤ)) h
  push_cast at hc
  push_cast
  linear_combination -hc

lemma code_valid (i j r A B : ℕ) (hri : r ≤ i) (hrj : r ≤ j) :
    Valid code (registers i j r A B) := by
  have hd : (r.factorial:ℤ)*(i-r).factorial*(j-r).factorial≠0 := by
    exact_mod_cast (Nat.ne_of_gt (denominator_pos i j r))
  change True ∧ True ∧ True ∧
    ((r.factorial:ℤ)*(i-r).factorial*(j-r).factorial≠0 ∧
      (r.factorial:ℤ)*(i-r).factorial*(j-r).factorial ∣ (i.factorial:ℤ)*j.factorial) ∧ True ∧ True ∧ True
  exact ⟨trivial,trivial,trivial,⟨hd,divisor i j r hri hrj⟩,trivial,trivial,trivial⟩

lemma code_result (i j r A B : ℕ) (hri : r ≤ i) (hrj : r ≤ j) :
    evaluate code (registers i j r A B) 0 =
      (A*B*(i.choose r*j.choose r*r.factorial) : ℕ) := by
  change ((i.factorial:ℤ)*j.factorial / ((r.factorial:ℤ)*(i-r).factorial*(j-r).factorial))*((A:ℤ)*B)=_
  rw [quotient i j r hri hrj]
  push_cast
  ring

/-- Every input register is bounded by the combined literal binary input size. -/
def inputSize (R : Fin 7→ℤ) : ℕ := ∑i : Fin 7, (signedBits (R i)).length

lemma input_bounded (R : Fin 7→ℤ) : Bounded (inputSize R) R := by
  intro i
  change (signedBits (R i)).length≤∑j : Fin 7, (signedBits (R j)).length
  exact Finset.single_le_sum (f:=fun j : Fin 7=>(signedBits (R j)).length) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)

/-- Actual finite-code execution of the crossing multiplicity and cached-count
product, with an unconditional polynomial in its encoded input registers. -/
theorem executes (g : BitString→ℕ) (i j r A B : ℕ) (hri : r ≤ i) (hrj : r ≤ j) :
    ∃cost, program.Executes g
      (store [] [] (signedBits ∘ registers i j r A B))
      (store [] [] (signedBits ∘ evaluate code (registers i j r A B))) cost ∧
      cost≤(straightTime code).eval (inputSize (registers i j r A B)) ∧
      (store [] [] (signedBits ∘ evaluate code (registers i j r A B))) (dataPort 0)=
        signedBits (A*B*(i.choose r*j.choose r*r.factorial) : ℕ) := by
  obtain ⟨t,ht,hb⟩ := compile_polynomial code g (registers i j r A B) _
    (input_bounded _) (code_valid i j r A B hri hrj)
  refine ⟨t,ht,hb,?_⟩
  simp only [store_data,Function.comp_def,code_result i j r A B hri hrj]

lemma queryFree : program.QueryFree := compile_queryFree code

/-- The pendant falling factorial is the same literal crossing program with
r=j; the two surplus factorials are harmless polynomial overhead. -/
theorem pendant_executes (g : BitString→ℕ) (i j A B : ℕ) (hji : j ≤ i) :
    ∃cost, program.Executes g
      (store [] [] (signedBits ∘ registers i j j A B))
      (store [] [] (signedBits ∘ evaluate code (registers i j j A B))) cost ∧
      cost≤(straightTime code).eval (inputSize (registers i j j A B)) ∧
      (store [] [] (signedBits ∘ evaluate code (registers i j j A B))) (dataPort 0)=
        signedBits (A*B*i.descFactorial j : ℕ) := by
  obtain ⟨t,ht,hb,ho⟩ := executes g i j j A B hji le_rfl
  refine ⟨t,ht,hb,ho.trans ?_⟩
  have he : A*B*(i.choose j*j.choose j*j.factorial)=A*B*i.descFactorial j := by
    rw [Nat.choose_self,Nat.descFactorial_eq_factorial_mul_choose]
    ring
  exact congrArg (fun z : ℕ=>signedBits (z:ℤ)) he

/-- The false-twin scalar product uses the same fixed finite code at zero
crossing indices, where every factorial is one. -/
theorem product_executes (g : BitString→ℕ) (A B : ℕ) :
    ∃cost, program.Executes g
      (store [] [] (signedBits ∘ registers 0 0 0 A B))
      (store [] [] (signedBits ∘ evaluate code (registers 0 0 0 A B))) cost ∧
      cost≤(straightTime code).eval (inputSize (registers 0 0 0 A B)) ∧
      (store [] [] (signedBits ∘ evaluate code (registers 0 0 0 A B))) (dataPort 0)=
        signedBits (A*B : ℕ) := by
  simpa only [Nat.choose_zero_right,Nat.factorial_zero,mul_one] using
    executes g 0 0 0 A B le_rfl le_rfl

end HiddenCircuits.DH.Runtime.CrossTerm
