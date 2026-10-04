import HiddenCircuits.Complexity.CNFGraph
import Mathlib.Data.Fin.Tuple.Basic

/-! A genuine parsimonious Tseitin construction for acyclic NAND circuits.
Every auxiliary gate bit is forced by an equivalence, not a clause-splitting chain. -/
namespace HiddenCircuits.Complexity

/-- An acyclic circuit; a newly appended gate may only read earlier wires. -/
inductive BoolCircuit (inputs : ℕ) : ℕ → Type
  | nil : BoolCircuit inputs 0
  | constant {gates : ℕ} (previous : BoolCircuit inputs gates) (value : Bool) :
      BoolCircuit inputs (gates+1)
  | snoc {gates : ℕ} (previous : BoolCircuit inputs gates)
      (left right : Fin (inputs+gates)) : BoolCircuit inputs (gates+1)

namespace BoolCircuit
variable {n m : ℕ}

def evaluate : {m : ℕ} → BoolCircuit n m → (Fin n → Bool) → (Fin (n+m) → Bool)
  | _, .nil, w => w
  | _, .constant C b, w => Fin.snoc (C.evaluate w) b
  | _, .snoc C a b, w =>
    Fin.snoc (C.evaluate w) (!(C.evaluate w a && C.evaluate w b))

def Compatible : {m : ℕ} → BoolCircuit n m → (Fin (n+m) → Bool) → Prop
  | _, .nil, _ => True
  | _, .constant C b, w => C.Compatible (fun i => w i.castSucc) ∧ w (Fin.last _) = b
  | _, .snoc C a b, w =>
    C.Compatible (fun i => w i.castSucc) ∧
    w (Fin.last (n+_)) = !(w a.castSucc && w b.castSucc)

abbrev RawCNF (α : Type*) := List (List (α × Bool))

def RawSatisfies {α : Type*} (f : RawCNF α) (w : α → Bool) : Prop :=
  ∀ c ∈ f, ∃ l ∈ c, w l.1 = l.2

/-- Exact equivalence z↔NAND(a,b), using three clauses. -/
def nandClauses {α : Type*} (a b z : α) : RawCNF α :=
  [[(a,true),(z,true)],[(b,true),(z,true)],[(a,false),(b,false),(z,false)]]

theorem nandClauses_correct {α : Type*} (a b z : α) (w : α → Bool) :
    RawSatisfies (nandClauses a b z) w ↔ w z = !(w a && w b) := by
  simp only [RawSatisfies,nandClauses,List.mem_cons,List.not_mem_nil,or_false,
    forall_eq_or_imp,forall_eq,exists_eq_or_imp,exists_eq,Prod.fst,Prod.snd]
  cases ha : w a <;> cases hb : w b <;> cases hz : w z <;> simp_all

lemma rawSatisfies_append {α : Type*} (f g : RawCNF α) (w : α → Bool) :
    RawSatisfies (f++g) w ↔ RawSatisfies f w ∧ RawSatisfies g w := by
  simp only [RawSatisfies,List.mem_append]
  constructor
  · intro h; exact ⟨fun c hc => h c (Or.inl hc),fun c hc => h c (Or.inr hc)⟩
  · rintro ⟨hf,hg⟩ c (hc | hc)
    · exact hf c hc
    · exact hg c hc

lemma rawSatisfies_map {α β : Type*} (f : RawCNF α) (e : α → β) (w : β → Bool) :
    RawSatisfies (f.map (List.map (fun l => (e l.1,l.2)))) w ↔
      RawSatisfies f (fun a => w (e a)) := by
  simp [RawSatisfies]

/-- Gate constraints have exactly three clauses per NAND gate. -/
def clauses : {m : ℕ} → BoolCircuit n m → RawCNF (Fin (n+m))
  | _, .nil => []
  | _, .constant C b =>
    C.clauses.map (List.map (fun l => (l.1.castSucc,l.2))) ++
      [[(Fin.last _,b)],[(Fin.last _,b)],[(Fin.last _,b)]]
  | _, .snoc C a b =>
    C.clauses.map (List.map (fun l => (l.1.castSucc,l.2))) ++
      nandClauses a.castSucc b.castSucc (Fin.last _)

@[simp] theorem clauses_length (C : BoolCircuit n m) : C.clauses.length = 3*m := by
  induction C with
  | nil => rfl
  | constant C b ih => simp [clauses,ih]; omega
  | snoc C a b ih => simp [clauses,nandClauses,ih]; omega

theorem clauses_correct (C : BoolCircuit n m) (w : Fin (n+m) → Bool) :
    RawSatisfies C.clauses w ↔ C.Compatible w := by
  induction C with
  | nil => simp [clauses,RawSatisfies,Compatible]
  | constant C b ih =>
    rw [clauses,rawSatisfies_append,rawSatisfies_map]
    simp only [ih,Compatible]
    simp [RawSatisfies]
  | snoc C a b ih =>
    rw [clauses,rawSatisfies_append,rawSatisfies_map,nandClauses_correct]
    exact and_congr (ih _) Iff.rfl

/-- Restriction to the original input wires. -/
def inputRestriction (w : Fin (n+m) → Bool) : Fin n → Bool := fun i => w (Fin.castAdd m i)

@[simp] theorem evaluate_input (C : BoolCircuit n m) (w : Fin n → Bool) :
    inputRestriction (C.evaluate w) = w := by
  funext i
  induction C with
  | nil => rfl
  | constant C b ih => simpa only [inputRestriction,evaluate,Fin.snoc_castAdd] using ih
  | snoc C a b ih =>
    simpa only [inputRestriction,evaluate,Fin.snoc_castAdd] using ih

theorem evaluate_compatible (C : BoolCircuit n m) (w : Fin n → Bool) :
    C.Compatible (C.evaluate w) := by
  induction C with
  | nil => trivial
  | constant C b ih => simpa [evaluate,Compatible] using ih
  | snoc C a b ih => simpa [evaluate,Compatible] using ih

/-- Every satisfying gate assignment is the canonical evaluation of its input.
This is the uniqueness missing from ordinary equisatisfiable clause splitting. -/
theorem compatible_unique (C : BoolCircuit n m) (w : Fin (n+m) → Bool)
    (hw : C.Compatible w) : w = C.evaluate (inputRestriction w) := by
  induction C with
  | nil => rfl
  | constant C b ih =>
    have hp := ih (fun i => w i.castSucc) hw.1
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [evaluate,Fin.snoc_last] using hw.2
    · simpa only [evaluate,Fin.snoc_castSucc] using congrFun hp j
  | snoc C a b ih =>
    have hp := ih (fun i => w i.castSucc) hw.1
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [evaluate,Fin.snoc_last]
      have ha : w a.castSucc = C.evaluate (inputRestriction w) a := congrFun hp a
      have hb : w b.castSucc = C.evaluate (inputRestriction w) b := congrFun hp b
      exact hw.2.trans (by rw [ha,hb])
    · simp only [evaluate,Fin.snoc_castSucc]
      exact congrFun hp j

/-- Add a unit clause requiring the selected output wire to be true. -/
def acceptingClauses (C : BoolCircuit n m) (out : Fin (n+m)) : RawCNF (Fin (n+m)) :=
  C.clauses ++ [[(out,true)]]

@[simp] theorem acceptingClauses_length (C : BoolCircuit n m) (out : Fin (n+m)) :
    (C.acceptingClauses out).length = 3*m+1 := by simp [acceptingClauses]

theorem acceptingClauses_correct (C : BoolCircuit n m) (out : Fin (n+m))
    (w : Fin (n+m) → Bool) :
    RawSatisfies (C.acceptingClauses out) w ↔ C.Compatible w ∧ w out = true := by
  rw [acceptingClauses,rawSatisfies_append,C.clauses_correct]
  simp [RawSatisfies]

noncomputable def acceptingAssignmentEquiv (C : BoolCircuit n m) (out : Fin (n+m)) :
    {w : Fin n → Bool // C.evaluate w out = true} ≃
    {v : Fin (n+m) → Bool // RawSatisfies (C.acceptingClauses out) v} where
  toFun w := ⟨C.evaluate w.val,(C.acceptingClauses_correct out _).mpr
    ⟨C.evaluate_compatible w.val,w.property⟩⟩
  invFun v := ⟨inputRestriction v.val,by
    have h := (C.acceptingClauses_correct out v.val).mp v.property
    rw [← C.compatible_unique v.val h.1]
    exact h.2⟩
  left_inv w := Subtype.ext (C.evaluate_input w.val)
  right_inv v := Subtype.ext (C.compatible_unique v.val
    ((C.acceptingClauses_correct out v.val).mp v.property).1).symm

/-- The actual arbitrary-CNF data consumed by the proved graph reduction. -/
def toCNF (C : BoolCircuit n m) (out : Fin (n+m)) :
    CNF (n+m) (C.acceptingClauses out).length where
  clause k := (C.acceptingClauses out).get k

theorem toCNF_satisfies_iff (C : BoolCircuit n m) (out : Fin (n+m)) (w : Fin (n+m) → Bool) :
    (C.toCNF out).Satisfies w ↔ RawSatisfies (C.acceptingClauses out) w := by
  constructor
  · intro h c hc
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hc
    simpa only [← hi] using h i
  · intro h i
    exact h _ (List.get_mem _ _)

/-- Parsimonious circuit-to-CNF count equality, retaining even unused input bits. -/
theorem toCNF_count (C : BoolCircuit n m) (out : Fin (n+m)) :
    (C.toCNF out).satCount = Fintype.card {w : Fin n → Bool // C.evaluate w out = true} := by
  classical
  unfold CNF.satCount
  apply Fintype.card_congr
  exact (Equiv.subtypeEquivRight (C.toCNF_satisfies_iff out)).trans
    (C.acceptingAssignmentEquiv out).symm

end BoolCircuit
end HiddenCircuits.Complexity
