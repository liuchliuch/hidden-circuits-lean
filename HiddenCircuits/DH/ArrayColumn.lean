import HiddenCircuits.DistanceHereditary
import HiddenCircuits.DH.MergeCost

/-! Executable, instrumented integer coefficient arrays for the normal-ordering recurrence.
The counter counts integer additions, subtractions, and multiplications. Array access,
allocation, natural-number indexing, and bit complexity are outside this arithmetic model. -/
namespace HiddenCircuits.DH
open Polynomial
open scoped BigOperators

namespace ArrayColumn

/-- A computation together with its count of integer arithmetic operations. -/
structure Counted (α : Type*) where
  value : α
  operations : ℕ
  deriving Repr

def mul (a b : ℤ) : Counted ℤ := ⟨a*b,1⟩
def add (a b : ℤ) : Counted ℤ := ⟨a+b,1⟩
def sub (a b : ℤ) : Counted ℤ := ⟨a-b,1⟩

/-- Reading outside the allocated coefficient array returns zero. -/
def read (c : Array ℤ) (k : ℕ) : ℤ := c[k]?.getD 0

/-- One sequential scan, appending the computed coefficients and accumulating their costs. -/
def scan (f : ℕ → Counted ℤ) : ℕ → Counted (Array ℤ)
  | 0 => ⟨#[],0⟩
  | n+1 =>
    let old := scan f n
    let next := f n
    ⟨old.value.push next.value, old.operations + next.operations⟩

@[simp] theorem scan_value (f : ℕ → Counted ℤ) (n : ℕ) :
    (scan f n).value = Array.ofFn (fun k : Fin n => (f k.val).value) := by
  induction n with
  | zero => simp [scan]
  | succ n ih => simp only [scan, ih, Array.ofFn_succ]; rfl

@[simp] theorem scan_size (f : ℕ → Counted ℤ) (n : ℕ) :
    (scan f n).value.size = n := by simp

/-- The loop counter is the sum of the arithmetic actually performed at its positions. -/
theorem scan_operations (f : ℕ → Counted ℤ) (n : ℕ) :
    (scan f n).operations = ∑ k ∈ Finset.range n, (f k).operations := by
  induction n with
  | zero => simp [scan]
  | succ n ih => simp [scan, ih, Finset.sum_range_succ]

@[simp] theorem read_scan (f : ℕ → Counted ℤ) (n k : ℕ) :
    read (scan f n).value k = if k < n then (f k).value else 0 := by
  by_cases h : k < n <;> simp [read, h]

/-- The four integer operations for one entry of X*current + current' - j*previous. -/
def entry (j : ℕ) (previous current : Array ℤ) (k : ℕ) : Counted ℤ :=
  let d := mul (k+1 : ℤ) (read current (k+1))
  let p := mul (j : ℤ) (read previous k)
  let s := add (if k = 0 then 0 else read current (k-1)) d.value
  let r := sub s.value p.value
  ⟨r.value,d.operations + p.operations + s.operations + r.operations⟩

@[simp] theorem entry_operations (j : ℕ) (p c : Array ℤ) (k : ℕ) :
    (entry j p c k).operations = 4 := rfl

/-- One materialized coefficient-array update. -/
def step (N j : ℕ) (previous current : Array ℤ) : Counted (Array ℤ) :=
  scan (entry j previous current) N

@[simp] theorem step_size (N j : ℕ) (p c : Array ℤ) :
    (step N j p c).value.size = N := by simp [step]

/-- A genuine scan of N entries performs exactly 4N integer operations. -/
@[simp] theorem step_operations (N j : ℕ) (p c : Array ℤ) :
    (step N j p c).operations = 4*N := by
  simp [step, scan_operations, Nat.mul_comm]

/-- Run the three-term recurrence, retaining two consecutive coefficient arrays. -/
def run (N : ℕ) (input : Array ℤ) : ℕ → Counted (Array ℤ × Array ℤ)
  | 0 => ⟨(#[],input),0⟩
  | j+1 =>
    let old := run N input j
    let next := step N j old.value.1 old.value.2
    ⟨(old.value.2,next.value),old.operations + next.operations⟩

/-- The scan cost is accumulated by the actual recurrence iteration. -/
theorem run_operations (N : ℕ) (input : Array ℤ) (b : ℕ) :
    (run N input b).operations = 4*b*N := by
  induction b with
  | zero => simp [run]
  | succ b ih => simp only [run, step_operations, ih]; ring

/-- Full coefficient refinement, including the zero tail beyond the array. -/
def Represents (c : Array ℤ) (F : ℤ[X]) : Prop := ∀ k, read c k = F.coeff k

@[simp] theorem read_empty (k : ℕ) : read #[] k = 0 := by simp [read]

@[simp] theorem read_of_ge_size (c : Array ℤ) (k : ℕ) (h : c.size ≤ k) :
    read c k = 0 := by simp [read, Array.getElem?_eq_none h]

lemma entry_value (j : ℕ) (p c : Array ℤ) (P C : ℤ[X])
    (hp : Represents p P) (hc : Represents c C) (k : ℕ) :
    (entry j p c k).value = (X*C + derivative C - (j : ℤ[X])*P).coeff k := by
  simp only [entry, mul, add, sub, coeff_sub, coeff_add, coeff_derivative,
    coeff_natCast_mul, hp k, hc (k+1)]
  cases k with
  | zero => simp
  | succ k => simp [hc k, coeff_X_mul]; ring

/-- A scan refines the polynomial recurrence whenever its output fits the array. -/
theorem step_represents (N j : ℕ) (p c : Array ℤ) (P C : ℤ[X])
    (hp : Represents p P) (hc : Represents c C)
    (hdegree : (X*C + derivative C - (j : ℤ[X])*P).natDegree < N) :
    Represents (step N j p c).value (X*C + derivative C - (j : ℤ[X])*P) := by
  intro k
  simp only [step, read_scan]
  split_ifs with hk
  · exact entry_value j p c P C hp hc k
  · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

/-- The column before Q₀ is zero, so the same executable step also computes Q₁. -/
noncomputable def previousColumn (F : ℤ[X]) : ℕ → ℤ[X]
  | 0 => 0
  | j+1 => matchingColumn F j

lemma recurrence_all (F : ℤ[X]) (j : ℕ) :
    X*matchingColumn F j + derivative (matchingColumn F j) -
      (j : ℤ[X])*previousColumn F j = matchingColumn F (j+1) := by
  cases j with
  | zero => simp [previousColumn, matchingColumn]
  | succ j => simpa [previousColumn, Nat.cast_add, Nat.cast_one] using (matchingColumn_recurrence F j).symm

/-- The actual executable loop agrees coefficientwise with every polynomial column
through the requested degree bound. -/
theorem run_represents (a b : ℕ) (input : Array ℤ) (F : ℤ[X])
    (hinput : Represents input F) (hdegree : F.natDegree ≤ a)
    (j : ℕ) (hj : j ≤ b) :
    Represents (run (a+b+1) input j).value.1 (previousColumn F j) ∧
    Represents (run (a+b+1) input j).value.2 (matchingColumn F j) := by
  induction j with
  | zero =>
    constructor
    · intro k; simp [run, previousColumn]
    · exact hinput
  | succ j ih =>
    obtain ⟨hp,hc⟩ := ih (by omega)
    constructor
    · exact hc
    · change Represents (step (a+b+1) j _ _).value (matchingColumn F (j+1))
      rw [← recurrence_all F j]
      apply step_represents _ _ _ _ _ _ hp hc
      rw [recurrence_all]
      have hd := matchingColumn_natDegree_le F (j+1)
      omega

/-- Interpret the finite coefficient array as an integer polynomial. -/
noncomputable def polynomial (c : Array ℤ) : ℤ[X] :=
  ∑ k ∈ Finset.range c.size, monomial k (read c k)

@[simp] theorem polynomial_coeff (c : Array ℤ) (k : ℕ) :
    (polynomial c).coeff k = read c k := by
  classical
  simp only [polynomial, finset_sum_coeff, coeff_monomial]
  by_cases hk : k < c.size
  · simp [Finset.mem_range, hk]
  · simp [Finset.mem_range, hk, read_of_ge_size c k (by omega)]

theorem polynomial_eq_of_represents (c : Array ℤ) (F : ℤ[X])
    (h : Represents c F) : polynomial c = F := by
  ext k
  exact (polynomial_coeff c k).trans (h k)

theorem represents_polynomial (c : Array ℤ) : Represents c (polynomial c) :=
  fun k => (polynomial_coeff c k).symm

/-- The length of an input coefficient array supplies the required degree bound. -/
theorem polynomial_natDegree_le (c : Array ℤ) (a : ℕ) (h : c.size ≤ a+1) :
    (polynomial c).natDegree ≤ a := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [polynomial_coeff]
  exact read_of_ge_size c k (by omega)

/-- The output array, interpreted as a polynomial, is exactly Q_b. -/
theorem run_polynomial (a b : ℕ) (input : Array ℤ) (F : ℤ[X])
    (hinput : Represents input F) (hdegree : F.natDegree ≤ a) :
    polynomial (run (a+b+1) input b).value.2 = matchingColumn F b :=
  polynomial_eq_of_represents _ _ (run_represents a b input F hinput hdegree b le_rfl).2

/-- A refinement statement with only an executable input-array length precondition. -/
theorem run_polynomial_of_size (a b : ℕ) (input : Array ℤ) (h : input.size ≤ a+1) :
    polynomial (run (a+b+1) input b).value.2 = matchingColumn (polynomial input) b :=
  run_polynomial a b input (polynomial input) (represents_polynomial input)
    (polynomial_natDegree_le input a h)

/-- Explicit rectangular arithmetic bound for the implemented loop. -/
theorem run_cost_bound (a b : ℕ) (input : Array ℤ) :
    (run (a+b+1) input b).operations ≤ 4*(b+1)*(a+b+1) := by
  rw [run_operations]
  nlinarith

/-- After orienting the smaller nonempty bag second, the actual loop uses at most 24ab
integer arithmetic operations. -/
theorem run_cost_le_pair_charge (a b : ℕ) (input : Array ℤ)
    (ha : b ≤ a) (hb : 1 ≤ b) :
    (run (a+b+1) input b).operations ≤ 24*a*b := by
  have h := recurrence_array_cost a b ha hb
  have hcost := run_cost_bound a b input
  nlinarith

/-- One multiplication and one addition accumulate a weighted column coefficient. -/
def addWeightedEntry (g : ℤ) (column total : Array ℤ) (k : ℕ) : Counted ℤ :=
  let term := mul g (read column k)
  let result := add (read total k) term.value
  ⟨result.value,term.operations + result.operations⟩

@[simp] theorem addWeightedEntry_operations (g : ℤ) (column total : Array ℤ) (k : ℕ) :
    (addWeightedEntry g column total k).operations = 2 := rfl

/-- Materialize the accumulator update total + g*column in one scan. -/
def addWeighted (N : ℕ) (g : ℤ) (column total : Array ℤ) : Counted (Array ℤ) :=
  scan (addWeightedEntry g column total) N

@[simp] theorem addWeighted_size (N : ℕ) (g : ℤ) (column total : Array ℤ) :
    (addWeighted N g column total).value.size = N := by simp [addWeighted]

@[simp] theorem addWeighted_operations (N : ℕ) (g : ℤ) (column total : Array ℤ) :
    (addWeighted N g column total).operations = 2*N := by
  simp [addWeighted, scan_operations, Nat.mul_comm]

theorem addWeighted_represents (N : ℕ) (g : ℤ) (column total : Array ℤ) (Q A : ℤ[X])
    (hq : Represents column Q) (ha : Represents total A)
    (hdegree : (A + C g*Q).natDegree < N) :
    Represents (addWeighted N g column total).value (A + C g*Q) := by
  intro k
  simp only [addWeighted, read_scan]
  split_ifs with hk
  · simp only [addWeightedEntry, mul, add, coeff_add, coeff_C_mul, hq k, ha k]
  · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

/-- Exactly the two most recent Q arrays and the accumulated weighted result are retained. -/
structure AccumState where
  previous : Array ℤ
  current : Array ℤ
  total : Array ℤ
  deriving Repr

/-- Compute Q₀ through Q_b and accumulate every weighted column, including g₀Q₀. -/
def runWeighted (N : ℕ) (input weights : Array ℤ) : ℕ → Counted AccumState
  | 0 =>
    let initial := addWeighted N (read weights 0) input #[]
    ⟨⟨#[],input,initial.value⟩,initial.operations⟩
  | j+1 =>
    let old := runWeighted N input weights j
    let next := step N j old.value.previous old.value.current
    let total := addWeighted N (read weights (j+1)) next.value old.value.total
    ⟨⟨old.value.current,next.value,total.value⟩,
      old.operations + next.operations + total.operations⟩

/-- Accumulation leaves the previously verified two-column recurrence unchanged. -/
theorem runWeighted_columns (N : ℕ) (input weights : Array ℤ) (b : ℕ) :
    (runWeighted N input weights b).value.previous = (run N input b).value.1 ∧
    (runWeighted N input weights b).value.current = (run N input b).value.2 := by
  induction b with
  | zero => exact ⟨rfl,rfl⟩
  | succ b ih =>
    simp only [runWeighted, run]
    constructor
    · exact ih.2
    · rw [ih.1,ih.2]

/-- The exact arithmetic count includes both all column updates and all accumulation scans. -/
theorem runWeighted_operations (N : ℕ) (input weights : Array ℤ) (b : ℕ) :
    (runWeighted N input weights b).operations = (6*b+2)*N := by
  induction b with
  | zero => simp [runWeighted]
  | succ b ih =>
    simp only [runWeighted, step_operations, addWeighted_operations, ih]
    ring

/-- The finite weighted column sum, through index b. -/
noncomputable def weightedSum (F G : ℤ[X]) (b : ℕ) : ℤ[X] :=
  ∑ j ∈ Finset.range (b+1), C (G.coeff j)*matchingColumn F j

@[simp] theorem weightedSum_zero (F G : ℤ[X]) :
    weightedSum F G 0 = C (G.coeff 0)*F := by simp [weightedSum]

lemma weightedSum_succ (F G : ℤ[X]) (b : ℕ) :
    weightedSum F G (b+1) = weightedSum F G b +
      C (G.coeff (b+1))*matchingColumn F (b+1) := by
  simp only [weightedSum, Finset.sum_range_succ]

theorem weightedSum_natDegree_le (F G : ℤ[X]) (b : ℕ) :
    (weightedSum F G b).natDegree ≤ F.natDegree+b := by
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have hd := (natDegree_C_mul_le (G.coeff j) (matchingColumn F j)).trans
    (matchingColumn_natDegree_le F j)
  have hjb := Finset.mem_range.mp hj
  omega

/-- Coefficient refinement for every accumulator prefix of the executable algorithm. -/
theorem runWeighted_represents (a b : ℕ) (input weights : Array ℤ) (F G : ℤ[X])
    (hinput : Represents input F) (hweights : Represents weights G) (hdegree : F.natDegree ≤ a)
    (j : ℕ) (hj : j ≤ b) :
    Represents (runWeighted (a+b+1) input weights j).value.total (weightedSum F G j) := by
  induction j with
  | zero =>
    change Represents (addWeighted (a+b+1) (read weights 0) input #[]).value _
    rw [weightedSum_zero, ← hweights 0, ← zero_add (C (read weights 0)*F)]
    apply addWeighted_represents _ _ _ _ _ _ hinput
    · intro k; simp
    · simp only [zero_add]
      have hd := natDegree_C_mul_le (read weights 0) F
      omega
  | succ j ih =>
    have ha := ih (by omega)
    have hq : Represents
        (step (a+b+1) j (runWeighted (a+b+1) input weights j).value.previous
          (runWeighted (a+b+1) input weights j).value.current).value
        (matchingColumn F (j+1)) := by
      change Represents (runWeighted (a+b+1) input weights (j+1)).value.current _
      rw [(runWeighted_columns _ _ _ _).2]
      exact (run_represents a b input F hinput hdegree (j+1) hj).2
    change Represents (addWeighted (a+b+1) (read weights (j+1)) _ _).value _
    rw [weightedSum_succ, ← hweights (j+1)]
    apply addWeighted_represents _ _ _ _ _ _ hq ha
    rw [hweights (j+1), ← weightedSum_succ]
    have hd := weightedSum_natDegree_le F G (j+1)
    omega

/-- The accumulator is the required sum of all weighted Q columns. -/
theorem runWeighted_polynomial (a b : ℕ) (input weights : Array ℤ) (F G : ℤ[X])
    (hinput : Represents input F) (hweights : Represents weights G) (hdegree : F.natDegree ≤ a) :
    polynomial (runWeighted (a+b+1) input weights b).value.total = weightedSum F G b :=
  polynomial_eq_of_represents _ _
    (runWeighted_represents a b input weights F G hinput hweights hdegree b le_rfl)

/-- The full true-twin polynomial operation sums over the actual support of G. -/
noncomputable def trueTwinProduct (F G : ℤ[X]) : ℤ[X] :=
  G.sum fun j g => C g*matchingColumn F j

lemma trueTwinProduct_eq_weightedSum (F G : ℤ[X]) (b : ℕ) (hdegree : G.natDegree ≤ b) :
    trueTwinProduct F G = weightedSum F G b := by
  exact G.sum_over_range' (fun j => by simp) (b+1) (by omega)

/-- The executable accumulator refines the entire true-twin operation, not just one Q column. -/
theorem runWeighted_product (a b : ℕ) (input weights : Array ℤ) (F G : ℤ[X])
    (hinput : Represents input F) (hweights : Represents weights G)
    (hf : F.natDegree ≤ a) (hg : G.natDegree ≤ b) :
    polynomial (runWeighted (a+b+1) input weights b).value.total = trueTwinProduct F G := by
  rw [trueTwinProduct_eq_weightedSum F G b hg]
  exact runWeighted_polynomial a b input weights F G hinput hweights hf

/-- Length-only preconditions suffice for the executable true-twin array operation. -/
theorem runWeighted_product_of_size (a b : ℕ) (input weights : Array ℤ)
    (hf : input.size ≤ a+1) (hg : weights.size ≤ b+1) :
    polynomial (runWeighted (a+b+1) input weights b).value.total =
      trueTwinProduct (polynomial input) (polynomial weights) :=
  runWeighted_product a b input weights (polynomial input) (polynomial weights)
    (represents_polynomial input) (represents_polynomial weights)
    (polynomial_natDegree_le input a hf) (polynomial_natDegree_le weights b hg)

/-- A rectangular bound for the complete column-and-accumulator computation. -/
theorem runWeighted_cost_bound (a b : ℕ) (input weights : Array ℤ) :
    (runWeighted (a+b+1) input weights b).operations ≤ 6*(b+1)*(a+b+1) := by
  rw [runWeighted_operations]
  nlinarith

/-- The complete true-twin update uses at most 36ab integer operations after orientation. -/
theorem runWeighted_cost_le_pair_charge (a b : ℕ) (input weights : Array ℤ)
    (ha : b ≤ a) (hb : 1 ≤ b) :
    (runWeighted (a+b+1) input weights b).operations ≤ 36*a*b := by
  have h := recurrence_array_cost a b ha hb
  have hcost := runWeighted_cost_bound a b input weights
  nlinarith

/-- Executable regression: 2Q₀+3Q₁+Q₂ for F=1+X². -/
example : (runWeighted 5 #[1,0,1] #[2,3,1] 2).value.total = #[4,9,7,3,1] := by decide

example : (runWeighted 5 #[1,0,1] #[2,3,1] 2).operations = 70 := by decide

/-- Executable regression test: Q₃ for F=1+X² is 6X+7X³+X⁵. -/
example : (run 6 #[1,0,1] 3).value.2 = #[0,6,0,7,0,1] := by decide

example : (run 6 #[1,0,1] 3).operations = 72 := by decide

end ArrayColumn
end HiddenCircuits.DH
