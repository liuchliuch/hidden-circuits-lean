import HiddenCircuits.Complexity.FiniteCNF

/-! Initial-row constraints for local Boolean tableaux. All tableau bits are
uniquely forced by the externally declared certificate bits; fixed bits and
negated copies introduce no extra assignments. -/
namespace HiddenCircuits.Complexity
open BoolCircuit
attribute [local instance] Classical.propDecidable

inductive InputSource (inputs : ℕ)
  | constant (value : Bool)
  | bit (index : Fin inputs) (negate : Bool)

namespace InputSource
variable {p : ℕ}
def evaluate : InputSource p → (Fin p → Bool) → Bool
  | .constant b, _ => b
  | .bit i negate, w => Bool.xor (w i) negate
end InputSource

namespace InitialNetwork
variable {p n r : ℕ}
abbrev Variable (p n t : ℕ) := Fin p ⊕ (Fin (t+1) × Fin n)

def initial (sources : Fin n → InputSource p) (input : Fin p → Bool) : Fin n → Bool :=
  fun v => (sources v).evaluate input

noncomputable def sourceClauses (t : ℕ) (v : Fin n) (s : InputSource p) : RawCNF (Variable p n t) :=
  match s with
  | .constant b => [[(Sum.inr (0,v),b)]]
  | .bit i negate => TruthTableCNF.clauses (fun _ : Fin 1 => Sum.inl i)
      (fun _ : Fin 1 => Sum.inr (0,v)) (fun a _ => Bool.xor (a 0) negate)

theorem sourceClauses_correct (t : ℕ) (v : Fin n) (s : InputSource p) (w : Variable p n t → Bool) :
    RawSatisfies (sourceClauses t v s) w ↔
      w (Sum.inr (0,v)) = s.evaluate (fun i => w (Sum.inl i)) := by
  cases s with
  | constant b => simp [sourceClauses,RawSatisfies,InputSource.evaluate]
  | bit i negate =>
    rw [sourceClauses,TruthTableCNF.clauses_correct]
    simp [InputSource.evaluate]

noncomputable def inputClauses (t : ℕ) (sources : Fin n → InputSource p) : RawCNF (Variable p n t) :=
  (List.ofFn (fun v => sourceClauses t v (sources v))).flatten

theorem inputClauses_correct (t : ℕ) (sources : Fin n → InputSource p) (w : Variable p n t → Bool) :
    RawSatisfies (inputClauses t sources) w ↔
      ∀ v, w (Sum.inr (0,v)) = initial sources (fun i => w (Sum.inl i)) v := by
  constructor
  · intro h v
    apply (sourceClauses_correct t v (sources v) w).mp
    intro c hc
    apply h c
    exact List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨v,rfl⟩,hc⟩
  · intro h c hc
    obtain ⟨cs,hcs,hc⟩ := List.mem_flatten.mp hc
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hcs
    exact (sourceClauses_correct t v (sources v) w).mpr (h v) c hc

noncomputable def clauses (N : LocalNetwork n r) (t : ℕ) (sources : Fin n → InputSource p)
    (out : Fin n) : RawCNF (Variable p n t) :=
  inputClauses t sources ++
    (N.acceptingClauses t out).map (List.map (fun l => (Sum.inr l.1,l.2)))

theorem clauses_correct (N : LocalNetwork n r) (t : ℕ) (sources : Fin n → InputSource p)
    (out : Fin n) (w : Variable p n t → Bool) :
    RawSatisfies (clauses N t sources out) w ↔
      (∀ v, w (Sum.inr (0,v)) = initial sources (fun i => w (Sum.inl i)) v) ∧
      RawSatisfies (N.acceptingClauses t out) (fun v => w (Sum.inr v)) := by
  rw [clauses,rawSatisfies_append,inputClauses_correct,rawSatisfies_map]

def canonical (N : LocalNetwork n r) (t : ℕ) (sources : Fin n → InputSource p)
    (input : Fin p → Bool) : Variable p n t → Bool
  | .inl i => input i
  | .inr iv => N.canonical t (initial sources input) iv

noncomputable def acceptingEquiv (N : LocalNetwork n r) (t : ℕ)
    (sources : Fin n → InputSource p) (out : Fin n) :
    {input : Fin p → Bool // (N.step^[t] (initial sources input)) out = true} ≃
    {w : Variable p n t → Bool // RawSatisfies (clauses N t sources out) w} where
  toFun w := ⟨canonical N t sources w.val,by
    apply (clauses_correct N t sources out _).mpr
    constructor
    · intro v; rfl
    · apply (N.acceptingClauses_correct t out _).mpr
      exact ⟨N.canonical_valid t _,w.property⟩⟩
  invFun w := ⟨fun i => w.val (Sum.inl i),by
    have h := (clauses_correct N t sources out w.val).mp w.property
    have ha := (N.acceptingClauses_correct t out _).mp h.2
    have hs : LocalNetwork.initial t (fun iv => w.val (Sum.inr iv)) =
        initial sources (fun i => w.val (Sum.inl i)) := funext h.1
    have he := congrFun (N.clauses_unique t (fun iv => w.val (Sum.inr iv)) ha.1) (Fin.last t,out)
    rw [hs] at he
    exact he.symm.trans ha.2⟩
  left_inv w := rfl
  right_inv w := by
    apply Subtype.ext
    funext v
    cases v with
    | inl i => rfl
    | inr iv =>
      have h := (clauses_correct N t sources out w.val).mp w.property
      have ha := (N.acceptingClauses_correct t out _).mp h.2
      have hs : LocalNetwork.initial t (fun iv => w.val (Sum.inr iv)) =
          initial sources (fun i => w.val (Sum.inl i)) := funext h.1
      have he := congrFun (N.clauses_unique t (fun iv => w.val (Sum.inr iv)) ha.1) iv
      rw [hs] at he
      exact he.symm

def variableEquiv (p n t : ℕ) : Variable p n t ≃ Fin (p+(t+1)*n) :=
  (Equiv.sumCongr (Equiv.refl (Fin p)) finProdFinEquiv).trans finSumFinEquiv

noncomputable def toCNF (N : LocalNetwork n r) (t : ℕ) (sources : Fin n → InputSource p)
    (out : Fin n) := reindexCNF (variableEquiv p n t) (clauses N t sources out)

/-- The actual CNF counts external certificate bits exactly once. -/
theorem toCNF_count (N : LocalNetwork n r) (t : ℕ) (sources : Fin n → InputSource p) (out : Fin n) :
    (toCNF N t sources out).satCount =
      Nat.card {input : Fin p → Bool // (N.step^[t] (initial sources input)) out = true} := by
  exact (reindexCNF_count (variableEquiv p n t) (clauses N t sources out)).trans
    (Nat.card_congr (acceptingEquiv N t sources out).symm)

end InitialNetwork
end HiddenCircuits.Complexity
