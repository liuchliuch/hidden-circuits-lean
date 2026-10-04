import HiddenCircuits.Complexity.CircuitCNF

/-! Local CNF truth-table constraints for a fixed finite Boolean transition.
The table has 2^n*m clauses; in the TM2 application n and m are fixed local
machine constants, not the global configuration or input length. -/
namespace HiddenCircuits.Complexity.TruthTableCNF
open BoolCircuit
variable {V : Type*} {n m : ℕ}

def mismatch (ports : Fin n → V) (a : Fin n → Bool) : List (V × Bool) :=
  List.ofFn (fun i => (ports i,!(a i)))

lemma bool_eq_not_iff (x y : Bool) : x = !y ↔ x ≠ y := by cases x <;> cases y <;> decide

lemma mismatch_satisfied (ports : Fin n → V) (a : Fin n → Bool) (w : V → Bool) :
    (∃ l ∈ mismatch ports a, w l.1 = l.2) ↔ ∃ i, w (ports i) ≠ a i := by
  simp [mismatch,bool_eq_not_iff]

def constraint (ports : Fin n → V) (output : V) (a : Fin n → Bool) (b : Bool) : List (V × Bool) :=
  mismatch ports a ++ [(output,b)]

lemma constraint_satisfied (ports : Fin n → V) (output : V) (a : Fin n → Bool)
    (b : Bool) (w : V → Bool) :
    (∃ l ∈ constraint ports output a b, w l.1 = l.2) ↔
      (∃ i, w (ports i) ≠ a i) ∨ w output = b := by
  simp only [constraint,List.mem_append,exists_prop,or_and_right,exists_or]
  rw [show (∃ l, l ∈ mismatch ports a ∧ w l.1 = l.2) ↔
    ∃ i, w (ports i) ≠ a i from mismatch_satisfied ports a w]
  simp

/-- All incorrect local output patterns are excluded, using the actual finite
truth table. No nondeterministic extension bits are introduced. -/
noncomputable def clauses (ports : Fin n → V) (outputs : Fin m → V)
    (f : (Fin n → Bool) → Fin m → Bool) : RawCNF V :=
  (Finset.univ : Finset (Fin n → Bool)).toList.flatMap (fun a =>
    List.ofFn (fun j => constraint ports (outputs j) a (f a j)))

theorem clauses_correct (ports : Fin n → V) (outputs : Fin m → V)
    (f : (Fin n → Bool) → Fin m → Bool) (w : V → Bool) :
    RawSatisfies (clauses ports outputs f) w ↔
      ∀ j, w (outputs j) = f (fun i => w (ports i)) j := by
  classical
  constructor
  · intro h j
    let a : Fin n → Bool := fun i => w (ports i)
    have hc : constraint ports (outputs j) a (f a j) ∈ clauses ports outputs f := by
      apply List.mem_flatMap.mpr
      refine ⟨a,by simp,?_⟩
      exact List.mem_ofFn.mpr ⟨j,rfl⟩
    rcases (constraint_satisfied ports (outputs j) a (f a j) w).mp (h _ hc) with hn | he
    · obtain ⟨i,hi⟩ := hn
      exact False.elim (hi rfl)
    · exact he
  · intro h c hc
    obtain ⟨a,_,hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hc
    apply (constraint_satisfied ports (outputs j) a (f a j) w).mpr
    by_cases he : a = (fun i => w (ports i))
    · exact Or.inr (by rw [he]; exact h j)
    · apply Or.inl
      by_contra hd
      push_neg at hd
      apply he
      funext i
      exact (hd i).symm

@[simp] theorem constraint_length (ports : Fin n → V) (output : V)
    (a : Fin n → Bool) (b : Bool) : (constraint ports output a b).length = n+1 := by
  simp [constraint,mismatch]

/-- Exact number of clauses, with all exponential dependence confined to the
local transition's input width. -/
theorem clauses_length (ports : Fin n → V) (outputs : Fin m → V)
    (f : (Fin n → Bool) → Fin m → Bool) :
    (clauses ports outputs f).length = 2^n*m := by
  classical
  simp [clauses,List.length_flatMap]

/-- All emitted clauses have the fixed local width n+1. -/
theorem clause_width (ports : Fin n → V) (outputs : Fin m → V)
    (f : (Fin n → Bool) → Fin m → Bool) (c : List (V × Bool))
    (hc : c ∈ clauses ports outputs f) : c.length = n+1 := by
  obtain ⟨a,_,hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hc
  exact constraint_length _ _ _ _

end HiddenCircuits.Complexity.TruthTableCNF
