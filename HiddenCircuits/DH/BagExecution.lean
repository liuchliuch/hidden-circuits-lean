import HiddenCircuits.DH.PolynomialCounts
import HiddenCircuits.DH.MergeCost

/-! Recursive execution of the three concrete bag-state updates.

A `BagExpr` supplies a binary merge schedule and its exact finite graph. The
numeric evaluator uses only the recurrence formulas, never graph-state
cardinalities. Its correctness is proved by induction from the matching
bijections. The efficient evaluator reuses computed child arrays and counts
integer coefficient additions, subtractions, and multiplications; allocation,
array access, index arithmetic, and graph preprocessing are outside that model. Constructing an expression from an ordinary distance-hereditary
input graph, and the graph-processing complexity of doing so, are separate
obligations not asserted by this file.
-/
namespace HiddenCircuits.DH
open scoped BigOperators

inductive BagExpr where
  | leaf
  | falseTwin (left right : BagExpr)
  | trueTwin (left right : BagExpr)
  | pendant (survivor absorbed : BagExpr)
  deriving DecidableEq, Repr

namespace BagExpr

/-- Each leaf is one original vertex; merges preserve distinct original vertices. -/
def Vertex : BagExpr → Type
  | .leaf => Unit
  | .falseTwin l r | .trueTwin l r | .pendant l r => Vertex l ⊕ Vertex r

instance vertexFintype : (e : BagExpr) → Fintype e.Vertex
  | .leaf => inferInstanceAs (Fintype Unit)
  | .falseTwin l r | .trueTwin l r | .pendant l r =>
    @instFintypeSum _ _ (vertexFintype l) (vertexFintype r)

/-- Size is maintained numerically, without enumerating graph vertices. -/
def size : BagExpr → ℕ
  | .leaf => 1
  | .falseTwin l r | .trueTwin l r | .pendant l r => l.size + r.size

@[simp] theorem card_vertex (e : BagExpr) : Fintype.card e.Vertex = e.size := by
  induction e with
  | leaf => rfl
  | falseTwin l r hl hr | trueTwin l r hl hr | pendant l r hl hr =>
    change Fintype.card (l.Vertex ⊕ r.Vertex) = l.size + r.size
    rw [Fintype.card_sum,hl,hr]

/-- Pendant merges close the absorbed boundary; twin merges retain both boundaries. -/
def active : (e : BagExpr) → Set e.Vertex
  | .leaf => Set.univ
  | .falseTwin l r | .trueTwin l r => {x | Sum.elim l.active r.active x}
  | .pendant l _ => {x | ∃ v ∈ l.active, x = Sum.inl v}

/-- The graph constructed by the supplied schedule, with its genuine cross-bag edges. -/
def graph : (e : BagExpr) → SimpleGraph e.Vertex
  | .leaf => ⊥
  | .falseTwin l r => disjointGraph l.graph r.graph
  | .trueTwin l r | .pendant l r => joinGraph l.graph r.graph l.active r.active

/-- Executable state recursion: a leaf has just one exposed vertex. -/
def state : BagExpr → ℕ → ℕ
  | .leaf, k => if k = 1 then 1 else 0
  | .falseTwin l r, k =>
    ∑ i : Fin (k+1), l.state i.val * r.state (k-i.val)
  | .trueTwin l r, k =>
    ∑ i : Fin (l.size+1), ∑ j : Fin (r.size+1), ∑ s : Fin (l.size+1),
      if i.val+j.val = k+2*s.val then
        l.state i.val * r.state j.val *
          (i.val.choose s.val * j.val.choose s.val * s.val.factorial) else 0
  | .pendant l r, k =>
    ∑ i : Fin (l.size+1), ∑ j : Fin (r.size+1),
      if i.val = k+j.val then l.state i.val * r.state j.val * i.val.descFactorial j.val else 0

private lemma leaf_matching (p : EncodedMatching (⊥ : SimpleGraph Unit)) :
    p.val = fun _ => none := by
  funext v
  cases h : p.val v with
  | none => rfl
  | some w => exact (p.property.2 v w h).elim

private lemma leaf_uncovered (p : EncodedMatching (⊥ : SimpleGraph Unit)) :
    uncovered p = 1 := by
  simp [uncovered,leaf_matching p]

private def leafState : BagState (⊥ : SimpleGraph Unit) Set.univ 1 :=
  ⟨⟨fun _ => none,by simp⟩,by simp [Admissible],by simp [uncovered]⟩

private theorem leaf_count (k : ℕ) :
    Fintype.card (BagState (⊥ : SimpleGraph Unit) Set.univ k) =
      if k = 1 then 1 else 0 := by
  classical
  by_cases hk : k = 1
  · subst k
    rw [if_pos rfl]
    apply Fintype.card_eq_one_iff.mpr
    refine ⟨leafState,?_⟩
    intro p
    apply Subtype.ext
    apply Subtype.ext
    exact leaf_matching p.val
  · rw [if_neg hk]
    haveI : IsEmpty (BagState (⊥ : SimpleGraph Unit) Set.univ k) :=
      ⟨fun p => hk ((leaf_uncovered p.val).symm.trans p.property.2).symm⟩
    exact Fintype.card_eq_zero

/-- Every executed state entry counts precisely the actual admissible graph matchings. -/
theorem state_correct (e : BagExpr) (k : ℕ) :
    e.state k = Fintype.card (BagState e.graph e.active k) := by
  induction e generalizing k with
  | leaf => exact (leaf_count k).symm
  | falseTwin l r hl hr =>
    rw [show (falseTwin l r).graph = disjointGraph l.graph r.graph from rfl]
    rw [show (falseTwin l r).active = {x | Sum.elim l.active r.active x} from rfl]
    rw [falseTwin_count]
    simp only [state,hl,hr]
  | trueTwin l r hl hr =>
    rw [show (trueTwin l r).graph = joinGraph l.graph r.graph l.active r.active from rfl]
    rw [show (trueTwin l r).active = {x | Sum.elim l.active r.active x} from rfl]
    rw [trueTwin_count,card_vertex,card_vertex]
    simp only [state,hl,hr]
  | pendant l r hl hr =>
    rw [show (pendant l r).graph = joinGraph l.graph r.graph l.active r.active from rfl]
    rw [show (pendant l r).active = {x | ∃ v ∈ l.active, x = Sum.inl v} from rfl]
    rw [pendant_count,card_vertex,card_vertex]
    simp only [state,hl,hr]

/-- Finalization reads state zero of the computed array, giving the graph's actual PM count. -/
theorem final_correct (e : BagExpr) : e.state 0 = perfectMatchingCount e.graph := by
  rw [state_correct,zeroState_card]

/-- The semantic bound is a consequence of execution correctness, not an assumed invariant. -/
theorem state_bound (e : BagExpr) (k : ℕ) : e.state k ≤ (e.size+1)^e.size := by
  rw [state_correct]
  simpa only [card_vertex] using bagState_card_bound (G := e.graph) e.active k

/-- Only finitely many computed entries can be nonzero. -/
theorem state_zero_of_size_lt (e : BagExpr) (k : ℕ) (h : e.size < k) : e.state k = 0 := by
  rw [state_correct]
  apply bagState_card_eq_zero_of_lt
  simpa only [card_vertex] using h

/-- Materialize the finite state array, retaining the exact zero tail convention. -/
def array (e : BagExpr) : Array ℕ := Array.ofFn (fun k : Fin (e.size+1) => e.state k.val)

theorem array_correct (e : BagExpr) (k : ℕ) :
    e.array[k]?.getD 0 = Fintype.card (BagState e.graph e.active k) := by
  by_cases hk : k < e.size+1
  · simp [array,hk,state_correct]
  · have hz := state_zero_of_size_lt e k (by omega)
    simp [array,hk,← state_correct,hz]

end BagExpr

namespace DirectArray
open ArrayColumn

/-- The two direct pair-scatter updates. True twins use `ArrayColumn.runWeighted`. -/
inductive Kind where
  | falseTwin
  | pendant
  deriving DecidableEq, Repr

def target : Kind → ℕ → ℕ → ℕ
  | .falseTwin, i, j => i+j
  | .pendant, i, j => i-j

def factor : Kind → ℕ → ℕ → ℤ
  | .falseTwin, _, _ => 1
  | .pendant, i, j => (i.descFactorial j : ℤ)

/-- A single coefficient accumulation, with its integer addition counted. -/
def addAt (out : Array ℤ) (k : ℕ) (term : ℤ) : Counted (Array ℤ) :=
  let s := add (read out k) term
  ⟨out.setIfInBounds k s.value,s.operations⟩

@[simp] theorem addAt_size (out : Array ℤ) (k : ℕ) (term : ℤ) :
    (addAt out k term).value.size = out.size := by simp [addAt]

@[simp] theorem addAt_operations (out : Array ℤ) (k : ℕ) (term : ℤ) :
    (addAt out k term).operations = 1 := rfl

theorem read_addAt (out : Array ℤ) (i : ℕ) (term : ℤ) (hi : i < out.size) (k : ℕ) :
    read (addAt out i term).value k = read out k + if i = k then term else 0 := by
  by_cases he : i = k
  · subst k; simp [addAt,ArrayColumn.add,ArrayColumn.read,hi]
  · simp [addAt,ArrayColumn.add,ArrayColumn.read,he]

/-- One direct-update row. Falling factorials are generated incrementally. -/
def row (kind : Kind) (i : ℕ) (x : ℤ) (weights out : Array ℤ) :
    ℕ → Counted (Array ℤ × ℤ)
  | 0 => ⟨(out,1),0⟩
  | j+1 =>
    let old := row kind i x weights out j
    let xy := mul x (read weights j)
    let term := mul xy.value old.value.2
    let next := addAt old.value.1 (target kind i j) term.value
    let fac := match kind with
      | .falseTwin => Counted.mk (1 : ℤ) 0
      | .pendant => mul (i-j : ℕ) old.value.2
    ⟨(next.value,fac.value),
      old.operations + xy.operations + term.operations + next.operations + fac.operations⟩

@[simp] theorem row_size (kind : Kind) (i : ℕ) (x : ℤ) (w out : Array ℤ) (n : ℕ) :
    (row kind i x w out n).value.1.size = out.size := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [row,addAt_size,ih]

@[simp] theorem row_factor (kind : Kind) (i : ℕ) (x : ℤ) (w out : Array ℤ) (n : ℕ) :
    (row kind i x w out n).value.2 = factor kind i n := by
  induction n with
  | zero => cases kind <;> simp [row,factor]
  | succ n ih => cases kind <;> simp [row,factor,ArrayColumn.mul,ih,Nat.descFactorial_succ]

/-- The counter includes coefficient products, additions, and factorial-factor updates. -/
theorem row_operations (kind : Kind) (i : ℕ) (x : ℤ) (w out : Array ℤ) (n : ℕ) :
    (row kind i x w out n).operations = (if kind = .falseTwin then 3 else 4)*n := by
  induction n with
  | zero => simp [row]
  | succ n ih => cases kind <;> simp [row,ArrayColumn.mul,ih] <;> omega

/-- A loop-prefix invariant for every output coefficient of a real scatter row. -/
theorem row_read (kind : Kind) (i : ℕ) (x : ℤ) (w out : Array ℤ) (n : ℕ)
    (hb : ∀ j < n, target kind i j < out.size) (k : ℕ) :
    read (row kind i x w out n).value.1 k = read out k +
      ∑ j ∈ Finset.range n, if target kind i j = k then x*read w j*factor kind i j else 0 := by
  induction n with
  | zero => simp [row]
  | succ n ih =>
    simp only [row,ArrayColumn.mul,row_factor]
    rw [read_addAt _ _ _ (by simpa only [row_size] using hb n (by omega))]
    rw [ih (fun j hj => hb j (by omega)),Finset.sum_range_succ]
    ring

/-- Visit each pair of child-state indices once, reusing the materialized output array. -/
def rows (kind : Kind) (b : ℕ) (input weights out : Array ℤ) : ℕ → Counted (Array ℤ)
  | 0 => ⟨out,0⟩
  | i+1 =>
    let old := rows kind b input weights out i
    let next := row kind i (read input i) weights old.value (b+1)
    ⟨next.value.1,old.operations + next.operations⟩

@[simp] theorem rows_size (kind : Kind) (b : ℕ) (input weights out : Array ℤ) (n : ℕ) :
    (rows kind b input weights out n).value.size = out.size := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rows,row_size,ih]

theorem rows_operations (kind : Kind) (b : ℕ) (input weights out : Array ℤ) (n : ℕ) :
    (rows kind b input weights out n).operations =
      (if kind = .falseTwin then 3 else 4)*n*(b+1) := by
  induction n with
  | zero => simp [rows]
  | succ n ih => simp only [rows,row_operations,ih]; ring

/-- The second loop-prefix invariant records exactly the pairs already processed. -/
theorem rows_read (kind : Kind) (b : ℕ) (input weights out : Array ℤ) (n : ℕ)
    (hb : ∀ i < n, ∀ j < b+1, target kind i j < out.size) (k : ℕ) :
    read (rows kind b input weights out n).value k = read out k +
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (b+1),
        if target kind i j = k then read input i*read weights j*factor kind i j else 0 := by
  induction n with
  | zero => simp [rows]
  | succ n ih =>
    simp only [rows]
    rw [row_read _ _ _ _ _ _ (fun j hj => by simpa only [rows_size] using hb n (by omega) j hj)]
    rw [ih (fun i hi j hj => hb i (by omega) j hj)]
    simp only [Finset.sum_range_succ]
    ring

/-- Both direct merges use a bounded allocated output and two finite index loops. -/
def run (kind : Kind) (a b : ℕ) (input weights : Array ℤ) : Counted (Array ℤ) :=
  rows kind b input weights (Array.replicate (a+b+1) 0) (a+1)

@[simp] theorem run_size (kind : Kind) (a b : ℕ) (input weights : Array ℤ) :
    (run kind a b input weights).value.size = a+b+1 := by simp [run]

theorem run_operations (kind : Kind) (a b : ℕ) (input weights : Array ℤ) :
    (run kind a b input weights).operations =
      (if kind = .falseTwin then 3 else 4)*(a+1)*(b+1) := by
  exact rows_operations _ _ _ _ _ _

/-- An explicit arithmetic bound for the actual direct loops. -/
theorem run_cost_le_pair_charge (kind : Kind) (a b : ℕ) (input weights : Array ℤ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (run kind a b input weights).operations ≤ 16*a*b := by
  rw [run_operations]
  have hp : (a+1)*(b+1) ≤ (2*a)*(2*b) := Nat.mul_le_mul (by omega) (by omega)
  split_ifs <;> nlinarith

theorem run_read (kind : Kind) (a b : ℕ) (input weights : Array ℤ) (k : ℕ) :
    read (run kind a b input weights).value k =
      ∑ i ∈ Finset.range (a+1), ∑ j ∈ Finset.range (b+1),
        if target kind i j = k then read input i*read weights j*factor kind i j else 0 := by
  rw [run,rows_read]
  · by_cases hk : k < a+b+1 <;> simp [ArrayColumn.read,hk]
  · intro i hi j hj
    simp only [Array.size_replicate]
    cases kind <;> simp only [target] <;> omega

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
variable {T : Set V} {U : Set W}

/-- Regrouping false-twin states by both child indices gives a rectangular pair scan. -/
theorem falseTwin_count_rectangle [Fintype V] [Fintype W] (k : ℕ) :
    Fintype.card (BagState (disjointGraph G H) {x | Sum.elim T U x} k) =
      ∑ i : Fin (Fintype.card V+1), ∑ j : Fin (Fintype.card W+1),
        if i.val+j.val = k then
          Fintype.card (BagState G T i.val)*Fintype.card (BagState H U j.val) else 0 := by
  classical
  let e : {pq : EncodedMatching G × EncodedMatching H //
      Admissible T pq.1 ∧ Admissible U pq.2 ∧ uncovered pq.1+uncovered pq.2 = k} ≃
      {pq : ActiveMatching G T × ActiveMatching H U //
        uncovered pq.1.val+uncovered pq.2.val = k} := {
    toFun := fun x => ⟨(⟨x.val.1,x.property.1⟩,⟨x.val.2,x.property.2.1⟩),x.property.2.2⟩
    invFun := fun x => ⟨(x.val.1.val,x.val.2.val),x.val.1.property,x.val.2.property,x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Fintype.card_congr ((falseTwinStateEquiv T U k).trans e)]
  rw [Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter,Fintype.sum_prod_type]
  have hq (p : ActiveMatching G T) :
      (∑ q : ActiveMatching H U, if uncovered p.val+uncovered q.val = k then 1 else 0) =
      ∑ j : Fin (Fintype.card W+1), Fintype.card (BagState H U j.val)*
        (if uncovered p.val+j.val = k then 1 else 0) :=
    sum_activeMatching (fun j => if uncovered p.val+j = k then 1 else 0)
  simp_rw [hq]
  rw [sum_activeMatching (G := G) (T := T)
    (fun i => ∑ j : Fin (Fintype.card W+1), Fintype.card (BagState H U j.val)*
      (if i+j.val = k then 1 else 0))]
  simp only [Finset.mul_sum,mul_ite,mul_zero,mul_one]

/-- The quadratic direct false-twin loop refines actual graph-state coefficients. -/
theorem run_falseTwin_bag [Fintype V] [Fintype W] (input weights : Array ℤ)
    (hp : Represents input (bagPolynomial G T))
    (hq : Represents weights (bagPolynomial H U)) :
    Represents (run .falseTwin (Fintype.card V) (Fintype.card W) input weights).value
      (bagPolynomial (disjointGraph G H) {x | Sum.elim T U x}) := by
  intro k
  rw [run_read,bagPolynomial_coeff,falseTwin_count_rectangle]
  simp only [Nat.cast_sum,Nat.cast_ite,Nat.cast_zero,Nat.cast_mul,
    ← Fin.sum_univ_eq_sum_range,target,factor,mul_one]
  simp_rw [show ∀ i, read input i = (bagPolynomial G T).coeff i from hp,
    show ∀ j, read weights j = (bagPolynomial H U).coeff j from hq,bagPolynomial_coeff]

/-- The quadratic direct pendant loop refines actual graph-state coefficients. -/
theorem run_pendant_bag [Fintype V] [Fintype W] (input weights : Array ℤ)
    (hp : Represents input (bagPolynomial G T))
    (hq : Represents weights (bagPolynomial H U)) :
    Represents (run .pendant (Fintype.card V) (Fintype.card W) input weights).value
      (bagPolynomial (joinGraph G H T U) {x | ∃ v ∈ T, x = Sum.inl v}) := by
  intro k
  rw [run_read,bagPolynomial_coeff,pendant_count]
  simp only [Nat.cast_sum,Nat.cast_ite,Nat.cast_zero,Nat.cast_mul,
    ← Fin.sum_univ_eq_sum_range,target,factor]
  simp_rw [show ∀ i, read input i = (bagPolynomial G T).coeff i from hp,
    show ∀ j, read weights j = (bagPolynomial H U).coeff j from hq,bagPolynomial_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hji : j.val ≤ i.val
  · have he : i.val-j.val = k ↔ i.val = k+j.val := by omega
    simp only [he]
  · have hz : i.val.descFactorial j.val = 0 := Nat.descFactorial_of_lt (by omega)
    have he : ¬i.val = k+j.val := by omega
    simp [hz,he]

end DirectArray
namespace BagExpr
open ArrayColumn

/-- The actual binary merge tree of the expression being executed. -/
def mergeTree : BagExpr → MergeTree
  | .leaf => .leaf
  | .falseTwin l r | .trueTwin l r | .pendant l r => .merge l.mergeTree r.mergeTree

@[simp] theorem mergeTree_size (e : BagExpr) : e.mergeTree.size = e.size := by
  induction e <;> simp_all [mergeTree,MergeTree.size,size]

theorem size_pos (e : BagExpr) : 0 < e.size := by
  simpa only [mergeTree_size] using e.mergeTree.size_pos

/-- Exchange only the polynomial operands when the left bag is smaller. -/
def trueRun (a b : ℕ) (input weights : Array ℤ) : Counted (Array ℤ) :=
  if b ≤ a then
    let result := runWeighted (a+b+1) input weights b
    ⟨result.value.total,result.operations⟩
  else
    let result := runWeighted (b+a+1) weights input a
    ⟨result.value.total,result.operations⟩

@[simp] theorem trueRun_size (a b : ℕ) (input weights : Array ℤ) :
    (trueRun a b input weights).value.size = a+b+1 := by
  unfold trueRun
  split <;> rename_i h
  · cases b <;> simp [runWeighted]
  · cases a <;> simp [runWeighted,Nat.add_comm]

/-- The oriented implementation still computes the original graph's true-twin states. -/
theorem trueRun_bag {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} {T : Set V} {U : Set W}
    (input weights : Array ℤ)
    (hp : Represents input (bagPolynomial G T))
    (hq : Represents weights (bagPolynomial H U)) :
    Represents (trueRun (Fintype.card V) (Fintype.card W) input weights).value
      (bagPolynomial (joinGraph G H T U) {x | Sum.elim T U x}) := by
  have he : polynomial (trueRun (Fintype.card V) (Fintype.card W) input weights).value =
      bagPolynomial (joinGraph G H T U) {x | Sum.elim T U x} := by
    unfold trueRun
    split
    · exact runWeighted_bag input weights hp hq
    · rw [runWeighted_product _ _ _ _ _ _ hq hp
        bagPolynomial_natDegree_le bagPolynomial_natDegree_le]
      rw [← trueTwinProduct_bag_comm,trueTwinProduct_bag]
  intro k
  rw [← polynomial_coeff,he]

/-- This bound is for the executed, oriented column-and-accumulation loops. -/
theorem trueRun_cost (a b : ℕ) (input weights : Array ℤ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (trueRun a b input weights).operations ≤ 36*a*b := by
  unfold trueRun
  split
  · exact runWeighted_cost_le_pair_charge a b input weights (by assumption) hb
  · have h := runWeighted_cost_le_pair_charge b a weights input (by omega) ha
    nlinarith

/-- A real recursive array execution. Child arrays are computed once and reused by a merge. -/
def execute : BagExpr → Counted (Array ℤ)
  | .leaf => ⟨#[0,1],0⟩
  | .falseTwin l r =>
    let left := execute l
    let right := execute r
    let next := DirectArray.run .falseTwin l.size r.size left.value right.value
    ⟨next.value,left.operations + right.operations + next.operations⟩
  | .trueTwin l r =>
    let left := execute l
    let right := execute r
    let next := trueRun l.size r.size left.value right.value
    ⟨next.value,left.operations + right.operations + next.operations⟩
  | .pendant l r =>
    let left := execute l
    let right := execute r
    let next := DirectArray.run .pendant l.size r.size left.value right.value
    ⟨next.value,left.operations + right.operations + next.operations⟩

@[simp] theorem execute_size (e : BagExpr) : e.execute.value.size = e.size+1 := by
  cases e <;> simp [execute,size]

/-- The recursive execution invariant connects every stored coefficient to its original graph. -/
theorem execute_correct (e : BagExpr) : Represents e.execute.value (bagPolynomial e.graph e.active) := by
  induction e with
  | leaf =>
    intro k
    rw [bagPolynomial_coeff,← state_correct]
    change read #[0,1] k = (if k = 1 then 1 else 0 : ℕ)
    cases k with
    | zero => rfl
    | succ k => cases k <;> simp [ArrayColumn.read]
  | falseTwin l r hl hr =>
    simpa only [execute,graph,active,card_vertex] using DirectArray.run_falseTwin_bag
      l.execute.value r.execute.value hl hr
  | trueTwin l r hl hr =>
    simpa only [execute,graph,active,card_vertex] using trueRun_bag
      l.execute.value r.execute.value hl hr
  | pendant l r hl hr =>
    simpa only [execute,graph,active,card_vertex] using DirectArray.run_pendant_bag
      l.execute.value r.execute.value hl hr

/-- The executable answer is the perfect-matching count of the constructed graph. -/
theorem execute_final_correct (e : BagExpr) :
    read e.execute.value 0 = (perfectMatchingCount e.graph : ℤ) := by
  rw [execute_correct,bagPolynomial_coeff,zeroState_card]

/-- The efficient array execution agrees with the independent elementary recurrence at every index. -/
theorem execute_state (e : BagExpr) (k : ℕ) : read e.execute.value k = (e.state k : ℤ) := by
  rw [execute_correct,bagPolynomial_coeff,← state_correct]

/-- Local arithmetic counters of the actual recursive execution are charged to its own merge tree. -/
theorem execute_cost_tree (e : BagExpr) : e.execute.operations ≤ 36*e.mergeTree.charge := by
  induction e with
  | leaf => simp [execute,mergeTree,MergeTree.charge]
  | falseTwin l r hl hr =>
    have h := DirectArray.run_cost_le_pair_charge .falseTwin l.size r.size
      l.execute.value r.execute.value (by have := l.size_pos; omega) (by have := r.size_pos; omega)
    simp only [execute,mergeTree,MergeTree.charge,mergeTree_size]
    nlinarith
  | trueTwin l r hl hr =>
    have h := trueRun_cost l.size r.size l.execute.value r.execute.value
      (by have := l.size_pos; omega) (by have := r.size_pos; omega)
    simp only [execute,mergeTree,MergeTree.charge,mergeTree_size]
    nlinarith
  | pendant l r hl hr =>
    have h := DirectArray.run_cost_le_pair_charge .pendant l.size r.size
      l.execute.value r.execute.value (by have := l.size_pos; omega) (by have := r.size_pos; omega)
    simp only [execute,mergeTree,MergeTree.charge,mergeTree_size]
    nlinarith

/-- An explicit quadratic arithmetic bound, conditional only on the supplied expression. -/
theorem execute_cost (e : BagExpr) : e.execute.operations ≤ 36*e.size.choose 2 := by
  simpa only [MergeTree.charge_eq_choose,mergeTree_size] using execute_cost_tree e

end BagExpr

namespace BagExpr

/-- A supplied graph isomorphism turns expression correctness into an ordinary-graph result. -/
theorem execute_final_correct_of_iso {V : Type*} [Fintype V]
    (e : BagExpr) (G : SimpleGraph V) (iso : e.graph ≃g G) :
    ArrayColumn.read e.execute.value 0 = (perfectMatchingCount G : ℤ) := by
  rw [execute_final_correct]
  congr 1
  have h := transport_bag_count iso e.active 0
  simpa only [zeroState_card] using h

/-- The size in the cost bound is the actual input-graph cardinality when a decomposition is supplied. -/
theorem execute_cost_of_iso {V : Type*} [Fintype V]
    (e : BagExpr) (G : SimpleGraph V) (iso : e.graph ≃g G) :
    e.execute.operations ≤ 36*(Fintype.card V).choose 2 := by
  have h := Fintype.card_congr iso.toEquiv
  rw [card_vertex] at h
  simpa only [h] using e.execute_cost

end BagExpr

namespace BagForest
open ArrayColumn

/-- Finalized bags form disjoint original vertex sets, including the empty graph. -/
def Vertex : List BagExpr → Type
  | [] => Empty
  | e :: es => e.Vertex ⊕ Vertex es

instance vertexFintype : (es : List BagExpr) → Fintype (Vertex es)
  | [] => inferInstanceAs (Fintype Empty)
  | e :: es => @instFintypeSum _ _ e.vertexFintype (vertexFintype es)

def graph : (es : List BagExpr) → SimpleGraph (Vertex es)
  | [] => ⊥
  | e :: es => disjointGraph e.graph (graph es)

def size (es : List BagExpr) : ℕ := (es.map BagExpr.size).sum

@[simp] theorem card_vertex (es : List BagExpr) : Fintype.card (Vertex es) = size es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    change Fintype.card (e.Vertex ⊕ Vertex es) = e.size + size es
    rw [Fintype.card_sum,BagExpr.card_vertex,ih]

/-- A single actual multiplication finalizes each computed bag. -/
def execute : List BagExpr → Counted ℤ
  | [] => ⟨1,0⟩
  | e :: es =>
    let head := e.execute
    let tail := execute es
    let result := mul (read head.value 0) tail.value
    ⟨result.value,head.operations + tail.operations + result.operations⟩

private theorem perfectMatchingCount_disjoint {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    perfectMatchingCount (disjointGraph G H) = perfectMatchingCount G * perfectMatchingCount H := by
  rw [← zeroState_card (G := disjointGraph G H) {x | Sum.elim (Set.univ : Set V) Set.univ x},
    falseTwin_count]
  change (∑ i : Fin 1, Fintype.card (BagState G Set.univ i.val) *
    Fintype.card (BagState H Set.univ (0-i.val))) = _
  rw [Fin.sum_univ_one]
  simp only [Fin.val_zero,Nat.sub_zero,zeroState_card]

private theorem perfectMatchingCount_empty : perfectMatchingCount (⊥ : SimpleGraph Empty) = 1 := by
  rw [← zeroState_card (G := (⊥ : SimpleGraph Empty)) Set.univ]
  apply Fintype.card_eq_one_iff.mpr
  let p : BagState (⊥ : SimpleGraph Empty) Set.univ 0 :=
    ⟨⟨(fun v => Empty.elim v),by simp⟩,by simp [Admissible],by simp [uncovered]⟩
  refine ⟨p,?_⟩
  intro q
  apply Subtype.ext
  apply Subtype.ext
  funext v
  exact v.elim

/-- Isolated finalization computes the PM count of the entire disjoint graph, including zero vertices. -/
theorem execute_correct (es : List BagExpr) :
    (execute es).value = (perfectMatchingCount (graph es) : ℤ) := by
  induction es with
  | nil =>
    change (1 : ℤ) = (perfectMatchingCount (⊥ : SimpleGraph Empty) : ℤ)
    rw [perfectMatchingCount_empty]; rfl
  | cons e es ih =>
    change read e.execute.value 0 * (execute es).value =
      (perfectMatchingCount (disjointGraph e.graph (graph es)) : ℤ)
    rw [BagExpr.execute_final_correct,ih,perfectMatchingCount_disjoint,Nat.cast_mul]

/-- Number of finalized nonempty bags is at most the number of original vertices. -/
theorem length_le_size (es : List BagExpr) : es.length ≤ size es := by
  induction es with
  | nil => simp [size]
  | cons e es ih =>
    have he := e.size_pos
    simp only [List.length_cons,size,List.map_cons,List.sum_cons] at *
    omega

/-- The actual forest counter is bounded using precisely its own constituent merge trees. -/
theorem execute_cost_forest (es : List BagExpr) :
    (execute es).operations ≤ 36*forestCharge (es.map BagExpr.mergeTree) + es.length := by
  induction es with
  | nil => simp [execute,forestCharge]
  | cons e es ih =>
    have he := e.execute_cost_tree
    simp only [execute,ArrayColumn.mul,List.map_cons,forestCharge,List.sum_cons,List.length_cons] at *
    omega

/-- Explicit quadratic merge cost and linear finalization cost for a complete expression forest. -/
theorem execute_cost (es : List BagExpr) :
    (execute es).operations ≤ 36*(size es).choose 2 + size es := by
  have h := forest_charge_le_choose (es.map BagExpr.mergeTree)
  have hs : forestSize (es.map BagExpr.mergeTree) = size es := by
    simp [forestSize,size,List.map_map,Function.comp_def]
  rw [hs] at h
  have he := execute_cost_forest es
  have hl := length_le_size es
  omega

/-- Combined correctness and concrete arithmetic complexity, conditional on a supplied forest. -/
theorem execute_spec (es : List BagExpr) :
    (execute es).value = (perfectMatchingCount (graph es) : ℤ) ∧
    (execute es).operations ≤ 36*(size es).choose 2 + size es :=
  ⟨execute_correct es,execute_cost es⟩

end BagForest

namespace BagForest

/-- End-to-end result for an ordinary finite graph with a supplied certified bag forest.
This theorem does not construct the forest or assert a preprocessing-time bound. -/
theorem execute_spec_of_iso {V : Type*} [Fintype V]
    (es : List BagExpr) (G : SimpleGraph V) (iso : graph es ≃g G) :
    (execute es).value = (perfectMatchingCount G : ℤ) ∧
    (execute es).operations ≤ 36*(Fintype.card V).choose 2 + Fintype.card V := by
  have hc := Fintype.card_congr iso.toEquiv
  rw [card_vertex] at hc
  constructor
  · rw [execute_correct]
    congr 1
    have h := transport_bag_count iso Set.univ 0
    simpa only [zeroState_card] using h
  · simpa only [hc] using execute_cost es

end BagForest

namespace BagExpr

/-- Executable regressions exercise each merge and the true-twin orientation branch. -/
example : (execute (falseTwin leaf leaf)).value = #[0,0,1] := by decide
example : (execute (pendant leaf leaf)).value = #[1,0,0] := by decide
example : (execute (trueTwin (falseTwin leaf leaf) (falseTwin leaf leaf))).value =
    #[2,0,4,0,1] := by decide
example : (execute (trueTwin (falseTwin leaf leaf) (falseTwin leaf leaf))).operations = 94 := by decide
example : (execute (trueTwin leaf (trueTwin leaf (trueTwin leaf leaf)))).value =
    #[3,0,6,0,1] := by decide
example : (execute (pendant (pendant leaf leaf) (pendant leaf leaf))).value =
    #[1,0,0,0,0] := by decide
example : (BagForest.execute []).value = 1 := by decide
example : (BagForest.execute [pendant leaf leaf,pendant leaf leaf]).value = 1 := by decide
example : (BagForest.execute [pendant leaf leaf,pendant leaf leaf]).operations = 34 := by decide

end BagExpr

namespace BagExpr

/-- The active set stays nonempty through each prescribed boundary update. -/
theorem active_nonempty (e : BagExpr) : e.active.Nonempty := by
  induction e with
  | leaf => exact ⟨(),Set.mem_univ _⟩
  | falseTwin l r hl hr | trueTwin l r hl hr =>
    obtain ⟨v,hv⟩ := hl
    exact ⟨Sum.inl v,hv⟩
  | pendant l r hl hr =>
    obtain ⟨v,hv⟩ := hl
    exact ⟨Sum.inl v,v,hv,rfl⟩

/-- Every stored state integer is nonnegative and bounded by the actual matching encoding. -/
theorem execute_entry_bound (e : BagExpr) (k : ℕ) :
    0 ≤ ArrayColumn.read e.execute.value k ∧
    ArrayColumn.read e.execute.value k ≤ (((e.size+1)^e.size : ℕ) : ℤ) := by
  rw [execute_state]
  exact ⟨Nat.cast_nonneg _,Int.ofNat_le.mpr (state_bound e k)⟩

theorem execute_entry_natAbs (e : BagExpr) (k : ℕ) :
    (ArrayColumn.read e.execute.value k).natAbs ≤ (e.size+1)^e.size := by
  rw [execute_state,Int.natAbs_natCast]
  exact state_bound e k

end BagExpr

end HiddenCircuits.DH
