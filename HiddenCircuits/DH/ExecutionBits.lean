import HiddenCircuits.DH.BagExecution
import HiddenCircuits.DH.ArithmeticBounds

/-! Integer-magnitude bounds for the concrete bag execution, including direct-loop
prefixes, scalar falling factors, products, scatter additions, and finalization.
The bounds use the same coefficient-arithmetic model as `BagExecution`.
-/
namespace HiddenCircuits.DH
open scoped BigOperators

namespace ExecutionBits
open ArrayColumn

/-- A nonnegative integer with a natural-number magnitude bound. -/
def ValueBound (M : ℕ) (z : ℤ) : Prop := 0 ≤ z ∧ z ≤ (M : ℤ)

def ArrayBound (M : ℕ) (a : Array ℤ) : Prop := ∀ k, ValueBound M (read a k)

def matchingEnvelope (n : ℕ) : ℕ := (n+1)^n

def directEnvelope (n : ℕ) : ℕ := (n+1)^2*(matchingEnvelope n)^3

lemma valueBound_zero (M : ℕ) : ValueBound M 0 := ⟨le_rfl,by positivity⟩

lemma valueBound_mono {M N : ℕ} {z : ℤ} (h : ValueBound M z) (hmn : M ≤ N) :
    ValueBound N z := ⟨h.1,h.2.trans (by exact_mod_cast hmn)⟩

lemma valueBound_mul {M N : ℕ} {x y : ℤ} (hx : ValueBound M x) (hy : ValueBound N y) :
    ValueBound (M*N) (x*y) := by
  refine ⟨mul_nonneg hx.1 hy.1,?_⟩
  rw [Nat.cast_mul]
  exact mul_le_mul hx.2 hy.2 hy.1 (by positivity)

lemma valueBound_add {M N : ℕ} {x y : ℤ} (hx : ValueBound M x) (hy : ValueBound N y) :
    ValueBound (M+N) (x+y) := by
  refine ⟨add_nonneg hx.1 hy.1,?_⟩
  rw [Nat.cast_add]
  exact add_le_add hx.2 hy.2

lemma valueBound_sum {I : Type*} (s : Finset I) (f : I → ℤ) (M : ℕ)
    (h : ∀ i ∈ s, ValueBound M (f i)) : ValueBound (s.card*M) (∑ i ∈ s, f i) := by
  constructor
  · exact Finset.sum_nonneg (fun i hi => (h i hi).1)
  · calc
      _ ≤ ∑ _i ∈ s, (M : ℤ) := Finset.sum_le_sum (fun i hi => (h i hi).2)
      _ = _ := by simp

lemma valueBound_natAbs {M : ℕ} {z : ℤ} (h : ValueBound M z) : z.natAbs ≤ M := by
  have hz : (z.natAbs : ℤ) = z := by rw [Int.natCast_natAbs,abs_of_nonneg h.1]
  have hb := h.2
  rw [← hz] at hb
  exact_mod_cast hb

lemma valueBound_bits {n M : ℕ} {z : ℤ} (h : ValueBound M z) (hm : M ≤ arithmeticEnvelope n) :
    z.natAbs.size ≤ (3*n+3)*(n+1).size+2 :=
  arithmeticEnvelope_bits n ((valueBound_natAbs h).trans hm)

lemma matchingEnvelope_pos (n : ℕ) : 0 < matchingEnvelope n := by
  unfold matchingEnvelope
  positivity

lemma directEnvelope_le_arithmetic (n : ℕ) : directEnvelope n ≤ arithmeticEnvelope n := by
  unfold directEnvelope matchingEnvelope arithmeticEnvelope
  calc
    (n+1)^2*((n+1)^n)^3 = (n+1)^(3*n+2) := by rw [← pow_mul,← pow_add]; congr 1; omega
    _ ≤ (n+1)^(3*n+3) := Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ 2*(n+1)^(3*n+3) := by omega

lemma cubeEnvelope_le_direct (n : ℕ) : (matchingEnvelope n)^3 ≤ directEnvelope n := by
  have hn : 0 < (n+1)^2 := by positivity
  simpa [directEnvelope] using Nat.mul_le_mul_right ((matchingEnvelope n)^3)
    (show 1 ≤ (n+1)^2 by omega)

lemma matchingEnvelope_le_direct (n : ℕ) : matchingEnvelope n ≤ directEnvelope n := by
  have hb := matchingEnvelope_pos n
  calc
    matchingEnvelope n = (matchingEnvelope n)^1 := by simp
    _ ≤ (matchingEnvelope n)^3 := Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ directEnvelope n := cubeEnvelope_le_direct n

lemma squareEnvelope_le_direct (n : ℕ) : (matchingEnvelope n)^2 ≤ directEnvelope n := by
  have hb := matchingEnvelope_pos n
  exact (Nat.pow_le_pow_right (by omega) (show 2 ≤ 3 by omega)).trans (cubeEnvelope_le_direct n)

/-- Falling factors never exceed the global matching envelope, even after they become zero. -/
lemma descFactorial_bound (n i j : ℕ) (hi : i ≤ n) : i.descFactorial j ≤ matchingEnvelope n := by
  by_cases hj : j ≤ i
  · calc
      i.descFactorial j ≤ i^j := Nat.descFactorial_le_pow i j
      _ ≤ (n+1)^j := Nat.pow_le_pow_left (by omega) j
      _ ≤ (n+1)^n := Nat.pow_le_pow_right (by omega) (by omega)
  · rw [Nat.descFactorial_of_lt (by omega)]
    exact Nat.zero_le _

lemma factor_bound (kind : DirectArray.Kind) (n i j : ℕ) (hi : i ≤ n) :
    ValueBound (matchingEnvelope n) (DirectArray.factor kind i j) := by
  cases kind with
  | falseTwin =>
    refine ⟨by simp [DirectArray.factor],?_⟩
    change (1 : ℤ) ≤ (matchingEnvelope n : ℤ)
    exact_mod_cast matchingEnvelope_pos n
  | pendant =>
    refine ⟨by simp [DirectArray.factor],?_⟩
    change (i.descFactorial j : ℤ) ≤ (matchingEnvelope n : ℤ)
    exact_mod_cast descFactorial_bound n i j hi

/-- Every coefficient array returned by a recursive subexpression has the global input bound. -/
theorem execute_array_bound (e : BagExpr) (n : ℕ) (hn : e.size ≤ n) :
    ArrayBound (matchingEnvelope n) e.execute.value := by
  intro k
  rw [BagExpr.execute_correct,bagPolynomial_coeff]
  constructor
  · positivity
  · exact_mod_cast (bagState_card_bound_of_card_le (G := e.graph) (T := e.active) n k
      (by simpa only [BagExpr.card_vertex] using hn))

/-- All coefficient products in a direct row, before the factorial multiplication. -/
lemma pairProduct_bound (n : ℕ) (input weights : Array ℤ)
    (hp : ArrayBound (matchingEnvelope n) input) (hq : ArrayBound (matchingEnvelope n) weights)
    (i j : ℕ) :
    ValueBound ((matchingEnvelope n)^2) (read input i*read weights j) := by
  simpa only [pow_two] using valueBound_mul (hp i) (hq j)

/-- All completed pair contributions, including the multiplication by the incremental factor. -/
lemma contribution_bound (kind : DirectArray.Kind) (n : ℕ) (input weights : Array ℤ)
    (hp : ArrayBound (matchingEnvelope n) input) (hq : ArrayBound (matchingEnvelope n) weights)
    (i j : ℕ) (hi : i ≤ n) :
    ValueBound ((matchingEnvelope n)^3)
      (read input i*read weights j*DirectArray.factor kind i j) := by
  have h := valueBound_mul (pairProduct_bound n input weights hp hq i j) (factor_bound kind n i j hi)
  simpa only [pow_succ] using h

/-- An array initialized with zeros introduces no uncontrolled values. -/
lemma replicate_zero_bound (N : ℕ) : ArrayBound 0 (Array.replicate N 0) := by
  intro k
  by_cases hk : k < N <;> simp [ValueBound,ArrayColumn.read,hk]

/-- Each completed-row prefix is bounded by the number of pairs already visited. -/
theorem rows_prefix_bound (kind : DirectArray.Kind) (a b n i : ℕ) (input weights : Array ℤ)
    (hp : ArrayBound (matchingEnvelope n) input) (hq : ArrayBound (matchingEnvelope n) weights)
    (ha : a ≤ n) (hi : i ≤ a+1) (k : ℕ) :
    ValueBound (i*(b+1)*(matchingEnvelope n)^3)
      (read (DirectArray.rows kind b input weights (Array.replicate (a+b+1) 0) i).value k) := by
  rw [DirectArray.rows_read]
  · have hz := replicate_zero_bound (a+b+1) k
    have hz' : read (Array.replicate (a+b+1) 0) k = 0 := by
      have := hz.1; have := hz.2; simp only [Nat.cast_zero] at *; omega
    rw [hz',zero_add]
    have hs := valueBound_sum (Finset.range i)
      (fun x => ∑ j ∈ Finset.range (b+1),
        if DirectArray.target kind x j = k then
          read input x*read weights j*DirectArray.factor kind x j else 0)
      ((b+1)*(matchingEnvelope n)^3) (by
        intro x hx
        have hxn : x ≤ n := by have := Finset.mem_range.mp hx; omega
        have ht := valueBound_sum (Finset.range (b+1))
          (fun j => if DirectArray.target kind x j = k then
            read input x*read weights j*DirectArray.factor kind x j else 0)
          ((matchingEnvelope n)^3) (by
            intro j hj
            dsimp only
            split_ifs
            · exact contribution_bound kind n input weights hp hq x j hxn
            · exact valueBound_zero _)
        simpa only [Finset.card_range] using ht)
    simpa only [Finset.card_range,Nat.mul_assoc] using hs
  · intro x hx j hj
    simp only [Array.size_replicate]
    cases kind <;> simp only [DirectArray.target] <;> omega

/-- The inner-row prefix starts from exactly the previously completed outer rows. -/
theorem row_prefix_bound (kind : DirectArray.Kind) (a b n i j : ℕ) (input weights : Array ℤ)
    (hp : ArrayBound (matchingEnvelope n) input) (hq : ArrayBound (matchingEnvelope n) weights)
    (ha : a ≤ n) (hi : i ≤ a) (hj : j ≤ b+1) (k : ℕ) :
    ValueBound ((i*(b+1)+j)*(matchingEnvelope n)^3)
      (read (DirectArray.row kind i (read input i) weights
        (DirectArray.rows kind b input weights (Array.replicate (a+b+1) 0) i).value j).value.1 k) := by
  rw [DirectArray.row_read]
  · have ho := rows_prefix_bound kind a b n i input weights hp hq ha (by omega) k
    have hs := valueBound_sum (Finset.range j)
      (fun s => if DirectArray.target kind i s = k then
        read input i*read weights s*DirectArray.factor kind i s else 0)
      ((matchingEnvelope n)^3) (by
        intro s hs
        dsimp only
        split_ifs
        · exact contribution_bound kind n input weights hp hq i s (by omega)
        · exact valueBound_zero _)
    have ht := valueBound_add ho hs
    simp only [Finset.card_range] at ht
    convert ht using 1; ring
  · intro s hs
    simp only [DirectArray.rows_size,Array.size_replicate]
    cases kind <;> simp only [DirectArray.target] <;> omega

lemma pairCount_le_square (a b n i j : ℕ) (ha : a ≤ n) (hb : b ≤ n)
    (hi : i ≤ a) (hj : j ≤ b+1) : i*(b+1)+j ≤ (n+1)^2 := by
  have hprod := Nat.mul_le_mul (show i+1 ≤ n+1 by omega) (show b+1 ≤ n+1 by omega)
  nlinarith

/-- Every partially accumulated output coefficient lies inside the fixed global envelope. -/
theorem row_prefix_global_bound (kind : DirectArray.Kind) (a b n i j : ℕ) (input weights : Array ℤ)
    (hp : ArrayBound (matchingEnvelope n) input) (hq : ArrayBound (matchingEnvelope n) weights)
    (ha : a ≤ n) (hb : b ≤ n) (hi : i ≤ a) (hj : j ≤ b+1) (k : ℕ) :
    ValueBound (directEnvelope n)
      (read (DirectArray.row kind i (read input i) weights
        (DirectArray.rows kind b input weights (Array.replicate (a+b+1) 0) i).value j).value.1 k) := by
  exact valueBound_mono (row_prefix_bound kind a b n i j input weights hp hq ha hi hj k)
    (Nat.mul_le_mul_right _ (pairCount_le_square a b n i j ha hb hi hj))

/-- The scatter's temporary sum equals the next materialized entry at its target index. -/
lemma row_add_eq_next (kind : DirectArray.Kind) (i j : ℕ) (x : ℤ) (weights out : Array ℤ)
    (ht : DirectArray.target kind i j < out.size) :
    read (DirectArray.row kind i x weights out j).value.1 (DirectArray.target kind i j) +
      x*read weights j*(DirectArray.row kind i x weights out j).value.2 =
    read (DirectArray.row kind i x weights out (j+1)).value.1 (DirectArray.target kind i j) := by
  simp only [DirectArray.row,ArrayColumn.mul]
  rw [DirectArray.read_addAt _ _ _ (by simpa only [DirectArray.row_size] using ht)]
  simp

/-- The scalar temporaries of an actual row step, in the same dependency order as `row`. -/
def rowScalars (kind : DirectArray.Kind) (i j : ℕ) (input weights out : Array ℤ) : List ℤ :=
  let old := DirectArray.row kind i (read input i) weights out j
  let xy := read input i*read weights j
  let term := xy*old.value.2
  [read input i,read weights j,old.value.2,xy,term,
    read old.value.1 (DirectArray.target kind i j),
    read old.value.1 (DirectArray.target kind i j)+term,
    match kind with
    | .falseTwin => 1
    | .pendant => (i-j : ℕ)*old.value.2]

/-- The direct implementation's individual scalar temporaries are bounded, not just its output. -/
theorem rowScalars_bound (kind : DirectArray.Kind) (a b n i j : ℕ) (input weights : Array ℤ)
    (hp : ArrayBound (matchingEnvelope n) input) (hq : ArrayBound (matchingEnvelope n) weights)
    (ha : a ≤ n) (hb : b ≤ n) (hi : i ≤ a) (hj : j ≤ b) :
    ∀ z ∈ rowScalars kind i j input weights
      (DirectArray.rows kind b input weights (Array.replicate (a+b+1) 0) i).value,
      ValueBound (directEnvelope n) z := by
  let out := (DirectArray.rows kind b input weights (Array.replicate (a+b+1) 0) i).value
  have hx := valueBound_mono (hp i) (matchingEnvelope_le_direct n)
  have hy := valueBound_mono (hq j) (matchingEnvelope_le_direct n)
  have hf : ValueBound (directEnvelope n)
      (DirectArray.row kind i (read input i) weights out j).value.2 := by
    rw [DirectArray.row_factor]
    exact valueBound_mono (factor_bound kind n i j (by omega)) (matchingEnvelope_le_direct n)
  have hxy := valueBound_mono (pairProduct_bound n input weights hp hq i j) (squareEnvelope_le_direct n)
  have hterm : ValueBound (directEnvelope n)
      (read input i*read weights j*(DirectArray.row kind i (read input i) weights out j).value.2) := by
    rw [DirectArray.row_factor]
    exact valueBound_mono (contribution_bound kind n input weights hp hq i j (by omega))
      (cubeEnvelope_le_direct n)
  have hold : ValueBound (directEnvelope n)
      (read (DirectArray.row kind i (read input i) weights out j).value.1 (DirectArray.target kind i j)) :=
    row_prefix_global_bound kind a b n i j input weights hp hq ha hb hi (by omega) _
  have hadd : ValueBound (directEnvelope n)
      (read (DirectArray.row kind i (read input i) weights out j).value.1 (DirectArray.target kind i j) +
        read input i*read weights j*(DirectArray.row kind i (read input i) weights out j).value.2) := by
    rw [row_add_eq_next]
    · exact row_prefix_global_bound kind a b n i (j+1) input weights hp hq ha hb hi (by omega) _
    · simp only [out,DirectArray.rows_size,Array.size_replicate]
      cases kind <;> simp only [DirectArray.target] <;> omega
  have hnext : ValueBound (directEnvelope n)
      (DirectArray.row kind i (read input i) weights out (j+1)).value.2 := by
    rw [DirectArray.row_factor]
    exact valueBound_mono (factor_bound kind n i (j+1) (by omega)) (matchingEnvelope_le_direct n)
  intro z hz
  change z ∈ rowScalars kind i j input weights out at hz
  simp only [rowScalars,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hx
  · exact hy
  · exact hf
  · exact hxy
  · exact hterm
  · exact hold
  · exact hadd
  · cases kind <;> simpa only [DirectArray.row,ArrayColumn.mul] using hnext

/-- Bit bound for every scalar expression in each direct merge iteration. -/
theorem rowScalars_bits (kind : DirectArray.Kind) (a b n i j : ℕ) (input weights : Array ℤ)
    (hp : ArrayBound (matchingEnvelope n) input) (hq : ArrayBound (matchingEnvelope n) weights)
    (ha : a ≤ n) (hb : b ≤ n) (hi : i ≤ a) (hj : j ≤ b)
    (z : ℤ) (hz : z ∈ rowScalars kind i j input weights
      (DirectArray.rows kind b input weights (Array.replicate (a+b+1) 0) i).value) :
    z.natAbs.size ≤ (3*n+3)*(n+1).size+2 :=
  valueBound_bits (rowScalars_bound kind a b n i j input weights hp hq ha hb hi hj z hz)
    (directEnvelope_le_arithmetic n)

/-- Every integer retained or evaluated by a direct merge, including all loop prefixes. -/
def DirectProperty (P : ℤ → Prop) (kind : DirectArray.Kind) (a b : ℕ) (input weights : Array ℤ) : Prop :=
  (∀ i ≤ a+1, ∀ k,
    P (read (DirectArray.rows kind b input weights (Array.replicate (a+b+1) 0) i).value k)) ∧
  (∀ i ≤ a, ∀ j ≤ b+1,
    (∀ k, P (read (DirectArray.row kind i (read input i) weights
      (DirectArray.rows kind b input weights (Array.replicate (a+b+1) 0) i).value j).value.1 k)) ∧
    P (DirectArray.row kind i (read input i) weights
      (DirectArray.rows kind b input weights (Array.replicate (a+b+1) 0) i).value j).value.2) ∧
  (∀ i ≤ a, ∀ j ≤ b, ∀ z ∈ rowScalars kind i j input weights
    (DirectArray.rows kind b input weights (Array.replicate (a+b+1) 0) i).value, P z) ∧
  (∀ i ≤ a, ∀ j ≤ b, P ((i-j : ℕ) : ℤ))

def DirectSafe (n : ℕ) (kind : DirectArray.Kind) (a b : ℕ) (input weights : Array ℤ) : Prop :=
  DirectProperty (fun z => z.natAbs ≤ arithmeticEnvelope n) kind a b input weights

theorem directSafe (kind : DirectArray.Kind) (a b n : ℕ) (input weights : Array ℤ)
    (hp : ArrayBound (matchingEnvelope n) input) (hq : ArrayBound (matchingEnvelope n) weights)
    (ha : a ≤ n) (hb : b ≤ n) : DirectSafe n kind a b input weights := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i hi k
    have h := rows_prefix_bound kind a b n i input weights hp hq ha hi k
    have hc : i*(b+1) ≤ (n+1)^2 := by
      have hm := Nat.mul_le_mul (show i ≤ n+1 by omega) (show b+1 ≤ n+1 by omega)
      simpa only [pow_two] using hm
    exact (valueBound_natAbs h).trans
      ((Nat.mul_le_mul_right _ hc).trans (directEnvelope_le_arithmetic n))
  · intro i hi j hj
    constructor
    · intro k
      exact (valueBound_natAbs (row_prefix_global_bound kind a b n i j input weights hp hq ha hb hi hj k)).trans
        (directEnvelope_le_arithmetic n)
    · rw [DirectArray.row_factor]
      exact (valueBound_natAbs (factor_bound kind n i j (by omega))).trans
        ((matchingEnvelope_le_direct n).trans (directEnvelope_le_arithmetic n))
  · intro i hi j hj z hz
    exact (valueBound_natAbs (rowScalars_bound kind a b n i j input weights hp hq ha hb hi hj z hz)).trans
      (directEnvelope_le_arithmetic n)

  · intro i hi j hj
    simp only [Int.natAbs_natCast]
    have hib : i ≤ matchingEnvelope n := by
      simpa only [Nat.descFactorial_one] using descFactorial_bound n i 1 (by omega)
    exact ((Nat.sub_le i j).trans hib).trans
      ((matchingEnvelope_le_direct n).trans (directEnvelope_le_arithmetic n))

/-- The direct-merge safety theorem applies to the actual recursively computed child arrays. -/
theorem directSafe_execute (kind : DirectArray.Kind) (l r : BagExpr) (n : ℕ)
    (hn : l.size+r.size ≤ n) :
    DirectSafe n kind l.size r.size l.execute.value r.execute.value :=
  directSafe kind l.size r.size n l.execute.value r.execute.value
    (execute_array_bound l n (by omega)) (execute_array_bound r n (by omega)) (by omega) (by omega)

/-- Every intermediate finalized suffix is itself the exact PM count of its disjoint graph. -/
theorem forest_value_bound (es : List BagExpr) (n : ℕ) (hn : BagForest.size es ≤ n) :
    ValueBound (matchingEnvelope n) (BagForest.execute es).value := by
  rw [BagForest.execute_correct,← zeroState_card (G := BagForest.graph es) Set.univ]
  constructor
  · positivity
  · exact_mod_cast (bagState_card_bound_of_card_le (G := BagForest.graph es) (T := Set.univ) n 0
      (by simpa only [BagForest.card_vertex] using hn))

/-- Each finalization multiplication's two operands and product satisfy the envelope. -/
theorem finalization_bound (e : BagExpr) (es : List BagExpr) (n : ℕ)
    (hn : BagForest.size (e :: es) ≤ n) :
    ValueBound (matchingEnvelope n) (read e.execute.value 0) ∧
    ValueBound (matchingEnvelope n) (BagForest.execute es).value ∧
    ValueBound (matchingEnvelope n) (read e.execute.value 0*(BagForest.execute es).value) := by
  have hs : BagForest.size (e :: es) = e.size+BagForest.size es := rfl
  rw [hs] at hn
  refine ⟨execute_array_bound e n (by omega) 0,forest_value_bound es n (by omega),?_⟩
  exact forest_value_bound (e :: es) n (by simpa only [hs] using hn)

/-- All finalization products, including intermediate suffix products, have O(n log n) bits. -/
theorem finalization_bits (e : BagExpr) (es : List BagExpr) (n : ℕ)
    (hn : BagForest.size (e :: es) ≤ n) :
    (read e.execute.value 0*(BagForest.execute es).value).natAbs.size ≤
      (3*n+3)*(n+1).size+2 :=
  valueBound_bits (finalization_bound e es n hn).2.2
    ((matchingEnvelope_le_direct n).trans (directEnvelope_le_arithmetic n))

lemma natAbs_le_of_abs_le {M : ℕ} {z : ℤ} (h : |z| ≤ (M : ℤ)) : z.natAbs ≤ M := by
  rw [← Int.natCast_natAbs] at h
  exact_mod_cast h

lemma linear_le_matchingEnvelope (n : ℕ) : n+1 ≤ matchingEnvelope n := by
  cases n with
  | zero => simp [matchingEnvelope]
  | succ n =>
    change n+1+1 ≤ (n+1+1)^(n+1)
    calc
      n+1+1 = (n+1+1)^1 := by simp
      _ ≤ (n+1+1)^(n+1) := Nat.pow_le_pow_right (by omega) (by omega)

/-- Integer scalar operands and transients evaluated in one real recurrence entry. -/
def entryScalars (j k : ℕ) (previous current : Array ℤ) : List ℤ :=
  let x := if k = 0 then 0 else read current (k-1)
  let d := (k+1 : ℤ)*read current (k+1)
  let p := (j : ℤ)*read previous k
  [(j : ℤ),(k+1 : ℤ),read previous k,read current (k+1),x,d,p,x+d,
    (entry j previous current k).value]

/-- All recurrence operands and transient arithmetic results fit the same envelope. -/
theorem entryScalars_bound (n j k : ℕ) (previous current : Array ℤ)
    (hj : j ≤ n) (hk : k ≤ n)
    (hp : ∀ l, |read previous l| ≤ (matchingEnvelope n : ℤ))
    (hc : ∀ l, |read current l| ≤ (matchingEnvelope n : ℤ)) :
    ∀ z ∈ entryScalars j k previous current, z.natAbs ≤ arithmeticEnvelope n := by
  have hB : (0 : ℤ) ≤ matchingEnvelope n := by positivity
  have hB1 : (1 : ℤ) ≤ matchingEnvelope n := by exact_mod_cast matchingEnvelope_pos n
  obtain ⟨hd,hp',hs,hr⟩ := entry_intermediate_bounds n j k previous current
    (matchingEnvelope n) hB hj hk hp hc
  have hj' : (j : ℤ) ≤ n := by exact_mod_cast hj
  have hk' : (k : ℤ) ≤ n := by exact_mod_cast hk
  have hx : |(if k = 0 then 0 else read current (k-1))| ≤ (matchingEnvelope n : ℤ) := by
    split_ifs
    · simp only [abs_zero]; exact hB
    · exact hc _
  have bound (z : ℤ) (h : |z| ≤ (2*n+2)*(matchingEnvelope n : ℤ)) :
      z.natAbs ≤ arithmeticEnvelope n := by
    apply le_trans _ (recurrenceEnvelope_le_arithmetic n)
    apply natAbs_le_of_abs_le
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,matchingEnvelope] using h
  intro z hz
  simp only [entryScalars,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply bound
    rw [abs_of_nonneg (by positivity : 0 ≤ (j : ℤ))]
    nlinarith
  · apply bound
    rw [abs_of_nonneg (by positivity : 0 ≤ (k+1 : ℤ))]
    nlinarith
  · exact bound _ ((hp k).trans (by nlinarith))
  · exact bound _ ((hc (k+1)).trans (by nlinarith))
  · exact bound _ (hx.trans (by nlinarith))
  · exact bound _ (hd.trans (by nlinarith))
  · exact bound _ (hp'.trans (by nlinarith))
  · exact bound _ (hs.trans (by nlinarith))
  · exact bound _ hr

variable {V W : Type*} [Fintype V] [Fintype W]
variable {G : SimpleGraph V} {H : SimpleGraph W} {T : Set V} {U : Set W}

/-- The already accumulated polynomial prefix, as an actual materialized array. -/
theorem weighted_total_bound (n j k : ℕ) (input weights : Array ℤ)
    (hp : Represents input (bagPolynomial G T)) (hq : Represents weights (bagPolynomial H U))
    (hj : j ≤ Fintype.card W) (hn : Fintype.card V+Fintype.card W ≤ n) :
    ValueBound ((n+1)*(matchingEnvelope n)^2)
      (read (runWeighted (Fintype.card V+Fintype.card W+1) input weights j).value.total k) := by
  have hr := runWeighted_represents (Fintype.card V) (Fintype.card W)
    input weights (bagPolynomial G T) (bagPolynomial H U)
    hp hq bagPolynomial_natDegree_le j hj
  rw [hr k]
  exact weightedSum_bag_coeff_bound (G := G) (H := H) (T := T) (U := U) j k n hj hn

/-- The column used by the weighted accumulator has the auxiliary-graph matching bound. -/
theorem weighted_current_bound (n j k : ℕ) (input weights : Array ℤ)
    (hp : Represents input (bagPolynomial G T))
    (hj : j ≤ Fintype.card W) (hn : Fintype.card V+Fintype.card W ≤ n) :
    ValueBound (matchingEnvelope n)
      (read (runWeighted (Fintype.card V+Fintype.card W+1) input weights j).value.current k) := by
  rw [(runWeighted_columns _ _ _ _).2]
  have hr := (run_represents (Fintype.card V) (Fintype.card W) input
    (bagPolynomial G T) hp bagPolynomial_natDegree_le j hj).2
  rw [hr k]
  exact matchingColumn_bag_coeff_bound (G := G) (T := T) j k n (by omega)

/-- The total before weighted column j is accumulated. -/
def previousTotal (N : ℕ) (input weights : Array ℤ) : ℕ → Array ℤ
  | 0 => #[]
  | j+1 => (runWeighted N input weights j).value.total

/-- Scalar multiplication and addition operands/results of an actual accumulation entry. -/
def weightedScalars (N : ℕ) (input weights : Array ℤ) (j k : ℕ) : List ℤ :=
  let column := (runWeighted N input weights j).value.current
  let before := previousTotal N input weights j
  [read weights j,read column k,read before k,read weights j*read column k,
    (addWeightedEntry (read weights j) column before k).value]

lemma weightedEntry_eq_total (N : ℕ) (input weights : Array ℤ) (j k : ℕ) (hk : k < N) :
    (addWeightedEntry (read weights j) (runWeighted N input weights j).value.current
      (previousTotal N input weights j) k).value =
      read (runWeighted N input weights j).value.total k := by
  cases j <;> simp only [runWeighted,previousTotal,addWeighted,read_scan,if_pos hk]

/-- The multiplication and temporary addition in each weighted scan are explicitly bounded. -/
theorem weightedScalars_bound (n j k : ℕ) (input weights : Array ℤ)
    (hp : Represents input (bagPolynomial G T)) (hq : Represents weights (bagPolynomial H U))
    (hj : j ≤ Fintype.card W) (hn : Fintype.card V+Fintype.card W ≤ n)
    (hk : k < Fintype.card V+Fintype.card W+1) :
    ∀ z ∈ weightedScalars (Fintype.card V+Fintype.card W+1) input weights j k,
      z.natAbs ≤ arithmeticEnvelope n := by
  have hweight : ValueBound (matchingEnvelope n) (read weights j) := by
    rw [hq j,bagPolynomial_coeff]
    constructor
    · positivity
    · exact_mod_cast (bagState_card_bound_of_card_le (G := H) (T := U) n j (by omega))
  have hcolumn := weighted_current_bound n j k input weights hp hj hn
  have hbefore : ValueBound ((n+1)*(matchingEnvelope n)^2)
      (read (previousTotal (Fintype.card V+Fintype.card W+1) input weights j) k) := by
    cases j with
    | zero => simpa only [previousTotal,read_empty] using valueBound_zero ((n+1)*(matchingEnvelope n)^2)
    | succ j => exact weighted_total_bound n j k input weights hp hq (by omega) hn
  have hprod := valueBound_mul hweight hcolumn
  have hout : ValueBound ((n+1)*(matchingEnvelope n)^2)
      ((addWeightedEntry (read weights j)
        (runWeighted (Fintype.card V+Fintype.card W+1) input weights j).value.current
        (previousTotal (Fintype.card V+Fintype.card W+1) input weights j) k).value) := by
    rw [weightedEntry_eq_total _ _ _ _ _ hk]
    exact weighted_total_bound n j k input weights hp hq hj hn
  have hb := (matchingEnvelope_le_direct n).trans (directEnvelope_le_arithmetic n)
  have hs := (squareEnvelope_le_direct n).trans (directEnvelope_le_arithmetic n)
  have ha : (n+1)*(matchingEnvelope n)^2 ≤ arithmeticEnvelope n := accumulationEnvelope_le_arithmetic n
  intro z hz
  simp only [weightedScalars,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl
  · exact (valueBound_natAbs hweight).trans hb
  · exact (valueBound_natAbs hcolumn).trans hb
  · exact (valueBound_natAbs hbefore).trans ha
  · exact (valueBound_natAbs hprod).trans (by simpa only [pow_two] using hs)
  · exact (valueBound_natAbs hout).trans ha

/-- Every stored column/accumulator and every primitive expression in the true-twin loop. -/
def TrueProperty (P : ℤ → Prop) (a b : ℕ) (input weights : Array ℤ) : Prop :=
  (∀ j ≤ b, ∀ k,
    P (read (runWeighted (a+b+1) input weights j).value.previous k) ∧
    P (read (runWeighted (a+b+1) input weights j).value.current k) ∧
    P (read (runWeighted (a+b+1) input weights j).value.total k)) ∧
  (∀ j < b, ∀ k < a+b+1,
    ∀ z ∈ entryScalars j k
      (runWeighted (a+b+1) input weights j).value.previous
      (runWeighted (a+b+1) input weights j).value.current, P z) ∧
  (∀ j ≤ b, ∀ k < a+b+1,
    ∀ z ∈ weightedScalars (a+b+1) input weights j k, P z)

def TrueSafe (n a b : ℕ) (input weights : Array ℤ) : Prop :=
  TrueProperty (fun z => z.natAbs ≤ arithmeticEnvelope n) a b input weights

/-- True-twin integer safety follows from auxiliary-graph counts at every recurrence prefix. -/
theorem trueSafe_bag (n : ℕ) (input weights : Array ℤ)
    (hp : Represents input (bagPolynomial G T)) (hq : Represents weights (bagPolynomial H U))
    (hn : Fintype.card V+Fintype.card W ≤ n) :
    TrueSafe n (Fintype.card V) (Fintype.card W) input weights := by
  have hpcol (j : ℕ) (hj : j ≤ Fintype.card W) (k : ℕ) :
      |read (runWeighted (Fintype.card V+Fintype.card W+1) input weights j).value.previous k| ≤
        (matchingEnvelope n : ℤ) := by
    rw [(runWeighted_columns _ _ _ _).1]
    exact (run_columns_abs_bound (Fintype.card W) j n input hp hj hn k).1
  have hccol (j : ℕ) (hj : j ≤ Fintype.card W) (k : ℕ) :
      |read (runWeighted (Fintype.card V+Fintype.card W+1) input weights j).value.current k| ≤
        (matchingEnvelope n : ℤ) := by
    rw [(runWeighted_columns _ _ _ _).2]
    exact (run_columns_abs_bound (Fintype.card W) j n input hp hj hn k).2
  have hb := (matchingEnvelope_le_direct n).trans (directEnvelope_le_arithmetic n)
  refine ⟨?_,?_,?_⟩
  · intro j hj k
    refine ⟨(natAbs_le_of_abs_le (hpcol j hj k)).trans hb,
      (natAbs_le_of_abs_le (hccol j hj k)).trans hb,?_⟩
    exact (valueBound_natAbs (weighted_total_bound n j k input weights hp hq hj hn)).trans
      (accumulationEnvelope_le_arithmetic n)
  · intro j hj k hk z hz
    exact entryScalars_bound n j k _ _ (by omega) (by omega)
      (hpcol j (by omega)) (hccol j (by omega)) z hz
  · intro j hj k hk z hz
    exact weightedScalars_bound n j k input weights hp hq hj hn hk z hz

/-- The true-twin operand exchange is reflected in the integer-safety statement. -/
def OrientedTrueProperty (P : ℤ → Prop) (a b : ℕ) (input weights : Array ℤ) : Prop :=
  if b ≤ a then TrueProperty P a b input weights else TrueProperty P b a weights input

def OrientedTrueSafe (n a b : ℕ) (input weights : Array ℤ) : Prop :=
  OrientedTrueProperty (fun z => z.natAbs ≤ arithmeticEnvelope n) a b input weights

theorem orientedTrueSafe_execute (l r : BagExpr) (n : ℕ) (hn : l.size+r.size ≤ n) :
    OrientedTrueSafe n l.size r.size l.execute.value r.execute.value := by
  unfold OrientedTrueSafe OrientedTrueProperty
  split
  · simpa only [BagExpr.card_vertex] using trueSafe_bag n l.execute.value r.execute.value
      l.execute_correct r.execute_correct (by simpa only [BagExpr.card_vertex] using hn)
  · simpa only [BagExpr.card_vertex] using trueSafe_bag n r.execute.value l.execute.value
      r.execute_correct l.execute_correct (by simpa only [BagExpr.card_vertex,Nat.add_comm] using hn)

/-- This predicate follows the actual recursive evaluator and includes its local loop traces. -/
def ExecutionProperty (P : ℤ → Prop) : BagExpr → Prop
  | .leaf => ∀ k, P (read BagExpr.leaf.execute.value k)
  | .falseTwin l r =>
    (∀ k, P (read (BagExpr.falseTwin l r).execute.value k)) ∧
    ExecutionProperty P l ∧ ExecutionProperty P r ∧
    DirectProperty P .falseTwin l.size r.size l.execute.value r.execute.value
  | .trueTwin l r =>
    (∀ k, P (read (BagExpr.trueTwin l r).execute.value k)) ∧
    ExecutionProperty P l ∧ ExecutionProperty P r ∧
    OrientedTrueProperty P l.size r.size l.execute.value r.execute.value
  | .pendant l r =>
    (∀ k, P (read (BagExpr.pendant l r).execute.value k)) ∧
    ExecutionProperty P l ∧ ExecutionProperty P r ∧
    DirectProperty P .pendant l.size r.size l.execute.value r.execute.value

def ExecutionSafe (n : ℕ) (e : BagExpr) : Prop :=
  ExecutionProperty (fun z => z.natAbs ≤ arithmeticEnvelope n) e

/-- Every coefficient, retained array prefix, and scalar temporary in the recursively
executed bag expression satisfies the common integer envelope. -/
theorem executionSafe (e : BagExpr) (n : ℕ) (hn : e.size ≤ n) : ExecutionSafe n e := by
  have harr (f : BagExpr) (hf : f.size ≤ n) (k : ℕ) :
      (read f.execute.value k).natAbs ≤ arithmeticEnvelope n :=
    (valueBound_natAbs (execute_array_bound f n hf k)).trans
      ((matchingEnvelope_le_direct n).trans (directEnvelope_le_arithmetic n))
  induction e with
  | leaf => exact harr .leaf hn
  | falseTwin l r hl hr =>
    change l.size+r.size ≤ n at hn
    exact ⟨harr _ hn,hl (by omega),hr (by omega),directSafe_execute .falseTwin l r n hn⟩
  | trueTwin l r hl hr =>
    change l.size+r.size ≤ n at hn
    exact ⟨harr _ hn,hl (by omega),hr (by omega),orientedTrueSafe_execute l r n hn⟩
  | pendant l r hl hr =>
    change l.size+r.size ≤ n at hn
    exact ⟨harr _ hn,hl (by omega),hr (by omega),directSafe_execute .pendant l r n hn⟩

/-- The forest predicate includes every bag computation and every finalization multiplication. -/
def ForestProperty (P : ℤ → Prop) : List BagExpr → Prop
  | [] => P 1
  | e :: es =>
    ExecutionProperty P e ∧ ForestProperty P es ∧
    P (read e.execute.value 0) ∧ P (BagForest.execute es).value ∧
    P (read e.execute.value 0*(BagForest.execute es).value)

def ForestSafe (n : ℕ) (es : List BagExpr) : Prop :=
  ForestProperty (fun z => z.natAbs ≤ arithmeticEnvelope n) es

/-- Complete integer-magnitude verification of the executable expression forest. -/
theorem forestSafe (es : List BagExpr) (n : ℕ) (hn : BagForest.size es ≤ n) : ForestSafe n es := by
  have hb := (matchingEnvelope_le_direct n).trans (directEnvelope_le_arithmetic n)
  induction es with
  | nil =>
    change (1 : ℤ).natAbs ≤ arithmeticEnvelope n
    have h := matchingEnvelope_pos n
    simpa only [Int.natAbs_one] using (show 1 ≤ arithmeticEnvelope n by omega)
  | cons e es ih =>
    have hs : e.size+BagForest.size es ≤ n := hn
    obtain ⟨he,ht,hm⟩ := finalization_bound e es n hn
    exact ⟨executionSafe e n (by omega),ih (by omega),
      (valueBound_natAbs he).trans hb,(valueBound_natAbs ht).trans hb,(valueBound_natAbs hm).trans hb⟩

/-- Kernel-checked integer safety and arithmetic correctness/cost for the same executable program. -/
theorem complete_execution_spec (es : List BagExpr) :
    (BagForest.execute es).value = (perfectMatchingCount (BagForest.graph es) : ℤ) ∧
    (BagForest.execute es).operations ≤
      36*(BagForest.size es).choose 2 + BagForest.size es ∧
    ForestSafe (BagForest.size es) es :=
  ⟨BagForest.execute_correct es,BagForest.execute_cost es,forestSafe es _ le_rfl⟩

/-- Strengthening a scalar property strengthens the entire observed direct-loop trace. -/
theorem directProperty_mono {P Q : ℤ → Prop} (hPQ : ∀ z, P z → Q z)
    {kind : DirectArray.Kind} {a b : ℕ} {input weights : Array ℤ}
    (h : DirectProperty P kind a b input weights) : DirectProperty Q kind a b input weights := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i hi k
    exact hPQ _ (h.1 i hi k)
  · intro i hi j hj
    exact ⟨fun k => hPQ _ ((h.2.1 i hi j hj).1 k),hPQ _ (h.2.1 i hi j hj).2⟩
  · intro i hi j hj z hz
    exact hPQ _ (h.2.2.1 i hi j hj z hz)
  · intro i hi j hj
    exact hPQ _ (h.2.2.2 i hi j hj)

theorem trueProperty_mono {P Q : ℤ → Prop} (hPQ : ∀ z, P z → Q z)
    {a b : ℕ} {input weights : Array ℤ}
    (h : TrueProperty P a b input weights) : TrueProperty Q a b input weights := by
  refine ⟨?_,?_,?_⟩
  · intro j hj k
    exact ⟨hPQ _ (h.1 j hj k).1,hPQ _ (h.1 j hj k).2.1,hPQ _ (h.1 j hj k).2.2⟩
  · intro j hj k hk z hz
    exact hPQ _ (h.2.1 j hj k hk z hz)
  · intro j hj k hk z hz
    exact hPQ _ (h.2.2 j hj k hk z hz)

theorem orientedTrueProperty_mono {P Q : ℤ → Prop} (hPQ : ∀ z, P z → Q z)
    {a b : ℕ} {input weights : Array ℤ}
    (h : OrientedTrueProperty P a b input weights) : OrientedTrueProperty Q a b input weights := by
  unfold OrientedTrueProperty at h ⊢
  by_cases hb : b ≤ a
  · simp only [if_pos hb] at h ⊢
    exact trueProperty_mono hPQ h
  · simp only [if_neg hb] at h ⊢
    exact trueProperty_mono hPQ h

theorem executionProperty_mono {P Q : ℤ → Prop} (hPQ : ∀ z, P z → Q z)
    (e : BagExpr) (h : ExecutionProperty P e) : ExecutionProperty Q e := by
  induction e with
  | leaf => exact fun k => hPQ _ (h k)
  | falseTwin l r hl hr | pendant l r hl hr =>
    exact ⟨fun k => hPQ _ (h.1 k),hl h.2.1,hr h.2.2.1,directProperty_mono hPQ h.2.2.2⟩
  | trueTwin l r hl hr =>
    exact ⟨fun k => hPQ _ (h.1 k),hl h.2.1,hr h.2.2.1,orientedTrueProperty_mono hPQ h.2.2.2⟩

theorem forestProperty_mono {P Q : ℤ → Prop} (hPQ : ∀ z, P z → Q z)
    (es : List BagExpr) (h : ForestProperty P es) : ForestProperty Q es := by
  induction es with
  | nil => exact hPQ 1 h
  | cons e es ih =>
    exact ⟨executionProperty_mono hPQ e h.1,ih h.2.1,
      hPQ _ h.2.2.1,hPQ _ h.2.2.2.1,hPQ _ h.2.2.2.2⟩

/-- O(n log n) magnitude bits for all array entries and scalar temporaries at every recursive node. -/
theorem execution_bits (e : BagExpr) (n : ℕ) (hn : e.size ≤ n) :
    ExecutionProperty (fun z => z.natAbs.size ≤ (3*n+3)*(n+1).size+2) e :=
  executionProperty_mono (fun _ hz => arithmeticEnvelope_bits n hz) e (executionSafe e n hn)

/-- The same bit bound includes empty initialization and all intermediate finalization products. -/
theorem forest_bits (es : List BagExpr) (n : ℕ) (hn : BagForest.size es ≤ n) :
    ForestProperty (fun z => z.natAbs.size ≤ (3*n+3)*(n+1).size+2) es :=
  forestProperty_mono (fun _ hz => arithmeticEnvelope_bits n hz) es (forestSafe es n hn)

/-- Explicit end-to-end arithmetic and bit complexity of the very same executable program. -/
theorem complete_execution_bit_spec (es : List BagExpr) :
    (BagForest.execute es).value = (perfectMatchingCount (BagForest.graph es) : ℤ) ∧
    (BagForest.execute es).operations ≤
      36*(BagForest.size es).choose 2 + BagForest.size es ∧
    ForestProperty (fun z => z.natAbs.size ≤
      (3*BagForest.size es+3)*(BagForest.size es+1).size+2) es :=
  ⟨BagForest.execute_correct es,BagForest.execute_cost es,forest_bits es _ le_rfl⟩

/-- Ordinary-graph form with an explicit supplied graph-decomposition witness.
Neither construction of that witness nor a preprocessing bound is assumed or asserted. -/
theorem complete_execution_bit_spec_of_iso {A : Type*} [Fintype A]
    (es : List BagExpr) (K : SimpleGraph A) (iso : BagForest.graph es ≃g K) :
    (BagForest.execute es).value = (perfectMatchingCount K : ℤ) ∧
    (BagForest.execute es).operations ≤ 36*(Fintype.card A).choose 2+Fintype.card A ∧
    ForestProperty (fun z => z.natAbs.size ≤
      (3*Fintype.card A+3)*(Fintype.card A+1).size+2) es := by
  have hc := Fintype.card_congr iso.toEquiv
  rw [BagForest.card_vertex] at hc
  obtain ⟨hval,hcost⟩ := BagForest.execute_spec_of_iso es K iso
  exact ⟨hval,hcost,forest_bits es (Fintype.card A) (by omega)⟩

end ExecutionBits
end HiddenCircuits.DH
