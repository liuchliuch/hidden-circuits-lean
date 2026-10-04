import HiddenCircuits.Complexity.CompilerSize

/-! Row-major tableau enumeration for the uniform emitter. Variable-sized cells
and times are traversed by explicit `List.ofFn` loops; only the fixed verifier's
local truth table retains a machine-constant enumeration. -/
namespace HiddenCircuits.Complexity
open BoolCircuit

namespace LocalNetwork
variable {n r : ℕ} (N : LocalNetwork n r)

noncomputable def orderedClauses (t : ℕ) : RawCNF (Variable (n := n) t) :=
  (List.ofFn (fun i : Fin t => (List.ofFn (fun v : Fin n => N.localClauses t i v)).flatten)).flatten

lemma mem_orderedClauses_iff (t : ℕ) (c : List (Variable (n := n) t × Bool)) :
    c ∈ N.orderedClauses t ↔ ∃ i : Fin t, ∃ v : Fin n, c ∈ N.localClauses t i v := by
  simp [orderedClauses]

theorem orderedClauses_correct (t : ℕ) (w : Variable (n := n) t → Bool) :
    RawSatisfies (N.orderedClauses t) w ↔ RawSatisfies (N.clauses t) w := by
  rw [N.clauses_correct]
  constructor
  · intro h i v
    apply (N.localClauses_correct t i v w).mp
    intro c hc
    exact h c ((N.mem_orderedClauses_iff t c).mpr ⟨i,v,hc⟩)
  · intro h c hc
    obtain ⟨i,v,hc⟩ := (N.mem_orderedClauses_iff t c).mp hc
    exact (N.localClauses_correct t i v w).mpr (h i v) c hc

@[simp] theorem orderedClauses_length (t : ℕ) : (N.orderedClauses t).length = t*n*2^r := by
  simp [orderedClauses,List.length_flatten,localClauses,TruthTableCNF.clauses_length,
    List.map_ofFn,Function.comp_def,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]

theorem orderedClause_width (t : ℕ) (c : List (Variable (n := n) t × Bool))
    (hc : c ∈ N.orderedClauses t) : c.length = r+1 := by
  obtain ⟨i,v,hc⟩ := (N.mem_orderedClauses_iff t c).mp hc
  exact TruthTableCNF.clause_width _ _ _ c hc

noncomputable def orderedAcceptingClauses (t : ℕ) (out : Fin n) : RawCNF (Variable (n := n) t) :=
  N.orderedClauses t ++ [[((Fin.last t,out),true)]]

theorem orderedAcceptingClauses_correct (t : ℕ) (out : Fin n) (w : Variable (n := n) t → Bool) :
    RawSatisfies (N.orderedAcceptingClauses t out) w ↔ RawSatisfies (N.acceptingClauses t out) w := by
  simp only [orderedAcceptingClauses,acceptingClauses,rawSatisfies_append,N.orderedClauses_correct]

@[simp] theorem orderedAcceptingClauses_length (t : ℕ) (out : Fin n) :
    (N.orderedAcceptingClauses t out).length = t*n*2^r+1 := by
  simp [orderedAcceptingClauses]

theorem orderedAcceptingClause_width (t : ℕ) (out : Fin n) (c : List (Variable (n := n) t × Bool))
    (hc : c ∈ N.orderedAcceptingClauses t out) : c.length ≤ r+2 := by
  rcases List.mem_append.mp hc with hc | hc
  · rw [N.orderedClause_width t c hc];omega
  · simp only [List.mem_singleton] at hc
    subst c;simp
end LocalNetwork

namespace InitialNetwork
variable {p n r : ℕ}

noncomputable def orderedClauses (N : LocalNetwork n r) (t : ℕ) (sources : Fin n → InputSource p)
    (out : Fin n) : RawCNF (Variable p n t) :=
  inputClauses t sources ++
    (N.orderedAcceptingClauses t out).map (List.map (fun l => (Sum.inr l.1,l.2)))

theorem orderedClauses_correct (N : LocalNetwork n r) (t : ℕ) (sources : Fin n → InputSource p)
    (out : Fin n) (w : Variable p n t → Bool) :
    RawSatisfies (orderedClauses N t sources out) w ↔ RawSatisfies (clauses N t sources out) w := by
  simp only [orderedClauses,clauses,rawSatisfies_append,rawSatisfies_map,N.orderedAcceptingClauses_correct]

theorem orderedClauses_length (N : LocalNetwork n r) (t : ℕ) (sources : Fin n → InputSource p) (out : Fin n) :
    (orderedClauses N t sources out).length ≤ 2*n+t*n*2^r+1 := by
  have h := inputClauses_length t sources
  simp only [orderedClauses,List.length_append,List.length_map,N.orderedAcceptingClauses_length]
  omega

theorem orderedClause_width (N : LocalNetwork n r) (t : ℕ) (sources : Fin n → InputSource p) (out : Fin n)
    (c : List (Variable p n t × Bool)) (hc : c ∈ orderedClauses N t sources out) : c.length ≤ r+2 := by
  rcases List.mem_append.mp hc with hc | hc
  · exact (inputClause_width t sources c hc).trans (by omega)
  · obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    simpa only [List.length_map] using N.orderedAcceptingClause_width t out d hd

noncomputable def orderedCNF (N : LocalNetwork n r) (t : ℕ) (sources : Fin n → InputSource p) (out : Fin n) :=
  reindexCNF (variableEquiv p n t) (orderedClauses N t sources out)

theorem orderedCNF_count (N : LocalNetwork n r) (t : ℕ) (sources : Fin n → InputSource p) (out : Fin n) :
    (orderedCNF N t sources out).satCount = (toCNF N t sources out).satCount := by
  rw [orderedCNF,toCNF,reindexCNF_count,reindexCNF_count]
  exact Nat.card_congr (Equiv.subtypeEquivRight (orderedClauses_correct N t sources out))

theorem orderedCNF_bits (N : LocalNetwork n r) (t : ℕ) (sources : Fin n → InputSource p) (out : Fin n) :
    (orderedCNF N t sources out).bits.length ≤
      10*(p+(t+1)*n+1)*(r+3)*(2*n+t*n*2^r+2) := by
  have hb := CNF.bits_length_le (orderedCNF N t sources out) (r+2)
    (reindexCNF_clause_width _ _ _ (orderedClause_width N t sources out))
  apply hb.trans
  apply Nat.mul_le_mul_left
  simpa only [List.length_map] using Nat.add_le_add_right (orderedClauses_length N t sources out) 1
end InitialNetwork

namespace VerifierTableau
open TM2BooleanEncoding
variable {v : BitString → Bool}
variable (M : Turing.TM2ComputableInPolyTime id Computability.encodeBool v)

noncomputable def orderedPositiveFormula (x : BitString) (m : ℕ) (ht : HasTrueSymbol M) :=
  InitialNetwork.orderedCNF (network M.tm (height M x m)) (horizon M x m)
    (sources M x m) (outputWire M x m ht)

noncomputable def orderedFormula (x : BitString) (m : ℕ) : CNFInput := by
  classical
  exact if ht : HasTrueSymbol M then ⟨_,_,orderedPositiveFormula M x m ht⟩ else ⟨m,1,rejectingCNF m⟩

lemma orderedFormula_pos (x : BitString) (m : ℕ) (ht : HasTrueSymbol M) :
    orderedFormula M x m = ⟨_,_,orderedPositiveFormula M x m ht⟩ := by
  unfold orderedFormula;exact dif_pos ht

lemma orderedFormula_neg (x : BitString) (m : ℕ) (ht : ¬ HasTrueSymbol M) :
    orderedFormula M x m = ⟨m,1,rejectingCNF m⟩ := by
  unfold orderedFormula;exact dif_neg ht

theorem orderedFormula_count (x : BitString) (m : ℕ) :
    (orderedFormula M x m).2.2.satCount = certificateCount v x m := by
  classical
  by_cases ht : HasTrueSymbol M
  · rw [orderedFormula_pos M x m ht]
    exact (InitialNetwork.orderedCNF_count _ _ _ _).trans (positiveFormula_count M x m ht)
  · rw [orderedFormula_neg M x m ht]
    exact (rejectingCNF_count m).trans (no_true_symbol_count M x m ht).symm

theorem orderedFormula_polynomial_size (p : Polynomial ℕ) (x : BitString) :
    (CNFInput.encode (orderedFormula M x (p.eval x.length))).length ≤ (formulaSizePolynomial M p).eval x.length := by
  classical
  rw [formulaSizePolynomial_eval]
  by_cases ht : HasTrueSymbol M
  · rw [orderedFormula_pos M x _ ht]
    exact (InitialNetwork.orderedCNF_bits _ _ _ _).trans (by omega)
  · rw [orderedFormula_neg M x _ ht]
    change (rejectingCNF (p.eval x.length)).bits.length ≤ _
    rw [rejectingCNF_bits];omega
end VerifierTableau

end HiddenCircuits.Complexity
