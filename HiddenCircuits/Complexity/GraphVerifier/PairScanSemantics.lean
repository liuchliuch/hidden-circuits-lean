import HiddenCircuits.Complexity.GraphVerifier.FlatVerifier

/-! The exact finite nested pair scan underlying the graph verifier. -/
namespace HiddenCircuits.Complexity.GraphVerifier

def EntryOK (n : ℕ) (payload witness : BitString) (i j : ℕ) : Prop :=
  bitAt payload (j+n*i)=bitAt payload (i+n*j) ∧
    (i=j → bitAt payload (j+n*i)=false) ∧
    (bitAt witness i=true → bitAt witness j=true → bitAt payload (j+n*i)=false)

instance (n : ℕ) (payload witness : BitString) (i j : ℕ) : Decidable (EntryOK n payload witness i j) :=
  inferInstanceAs (Decidable (_ = _ ∧ (_ = _ → _ = _) ∧ (_ = _ → _ = _ → _ = _)))

def entryFlag (n : ℕ) (payload witness : BitString) (i j : ℕ) : Bool :=
  decide (EntryOK n payload witness i j)

def scanPairs (n : ℕ) (payload witness : BitString) : Bool :=
  (List.range n).all (fun i => (List.range n).all (fun j => entryFlag n payload witness i j))

 theorem flatEdge_eq (n : ℕ) (payload : BitString) (i j : Fin n) :
    flatEdge n payload i j=bitAt payload (j.val+n*i.val) := rfl

 theorem scanPairs_iff (n : ℕ) (payload witness : BitString) : scanPairs n payload witness=true ↔
    (∀ i j : Fin n, flatEdge n payload i j=flatEdge n payload j i) ∧
      (∀ i : Fin n, flatEdge n payload i i=false) ∧ ValidSelectedPairs n payload witness := by
  simp only [scanPairs,List.all_eq_true,List.mem_range,entryFlag,decide_eq_true_eq]
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · intro i j
      exact (h i.val i.isLt j.val j.isLt).1
    · intro i
      exact (h i.val i.isLt i.val i.isLt).2.1 rfl
    · intro i j hi hj
      exact (h i.val i.isLt j.val j.isLt).2.2 hi hj
  · rintro ⟨hs,hl,hw⟩ i hi j hj
    refine ⟨hs ⟨i,hi⟩ ⟨j,hj⟩,?_,hw ⟨i,hi⟩ ⟨j,hj⟩⟩
    intro he
    subst j
    exact hl ⟨i,hi⟩

/-- The pair scanner is exactly both the ordinary graph-validation and independent-set tests. -/
theorem scanPairs_payload (n : ℕ) (payload witness : BitString) :
    (decide (payload.length=n*n) && scanPairs n payload witness)=
      (decide (ValidPayload n payload) && decide (ValidSelectedPairs n payload witness)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true,decide_eq_true_eq,scanPairs_iff,ValidPayload]
  tauto

/-- The Boolean truth table compiled in the fixed per-pair decision block. -/
def pairDecision (forward backward selectedLeft selectedRight diagonal accumulator : Bool) : Bool :=
  accumulator && (forward==backward) && !(diagonal && forward) && !(selectedLeft && selectedRight && forward)

 theorem pairDecision_correct (n : ℕ) (payload witness : BitString) (i j : ℕ) (a : Bool) :
    pairDecision (bitAt payload (j+n*i)) (bitAt payload (i+n*j))
      (bitAt witness i) (bitAt witness j) (decide (i=j)) a=(a && entryFlag n payload witness i j) := by
  unfold pairDecision entryFlag EntryOK
  by_cases hij : i=j <;> simp only [hij,decide_true,decide_false]
  all_goals cases h₁ : bitAt payload (j+n*i) <;> cases h₂ : bitAt payload (i+n*j) <;>
    cases h₃ : bitAt witness i <;> cases h₄ : bitAt witness j <;> cases a <;> simp_all

end HiddenCircuits.Complexity.GraphVerifier
