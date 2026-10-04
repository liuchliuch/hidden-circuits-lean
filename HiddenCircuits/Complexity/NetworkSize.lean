import HiddenCircuits.Complexity.InitialNetworkCNF
import HiddenCircuits.Complexity.CNFSize
import HiddenCircuits.Complexity.VerifierCNF

/-! Structural and actual binary-size bounds for the constructed verifier CNFs. -/
namespace HiddenCircuits.Complexity
open BoolCircuit

namespace LocalNetwork
variable {n r : ℕ} (N : LocalNetwork n r)

theorem clause_width (t : ℕ) (c : List (Variable (n := n) t × Bool)) (hc : c ∈ N.clauses t) :
    c.length = r+1 := by
  obtain ⟨⟨i,v⟩,_,hc⟩ := List.mem_flatMap.mp hc
  exact TruthTableCNF.clause_width _ _ _ c hc

theorem acceptingClause_width (t : ℕ) (out : Fin n) (c : List (Variable (n := n) t × Bool))
    (hc : c ∈ N.acceptingClauses t out) : c.length ≤ r+2 := by
  rcases List.mem_append.mp hc with hc | hc
  · rw [N.clause_width t c hc];omega
  · simp only [List.mem_singleton] at hc
    subst c
    simp
end LocalNetwork

namespace InitialNetwork
variable {p n r : ℕ}

theorem sourceClauses_length (t : ℕ) (v : Fin n) (s : InputSource p) :
    (sourceClauses t v s).length ≤ 2 := by
  cases s <;> simp [sourceClauses,TruthTableCNF.clauses_length]

theorem sourceClause_width (t : ℕ) (v : Fin n) (s : InputSource p)
    (c : List (Variable p n t × Bool)) (hc : c ∈ sourceClauses t v s) : c.length ≤ 2 := by
  cases s with
  | constant b =>
    simp only [sourceClauses,List.mem_singleton] at hc
    subst c
    simp
  | bit i negate =>
    exact (TruthTableCNF.clause_width _ _ _ c hc).le

theorem inputClauses_length (t : ℕ) (sources : Fin n → InputSource p) :
    (inputClauses t sources).length ≤ 2*n := by
  have h := list_sum_map_le (List.ofFn (fun v => sourceClauses t v (sources v))) List.length 2 (by
    intro c hc
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hc
    exact sourceClauses_length t v (sources v))
  simpa [inputClauses,List.length_flatten] using h

theorem inputClause_width (t : ℕ) (sources : Fin n → InputSource p)
    (c : List (Variable p n t × Bool)) (hc : c ∈ inputClauses t sources) : c.length ≤ 2 := by
  obtain ⟨cs,hcs,hc⟩ := List.mem_flatten.mp hc
  obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hcs
  exact sourceClause_width t v (sources v) c hc

theorem clauses_length (N : LocalNetwork n r) (t : ℕ) (sources : Fin n → InputSource p) (out : Fin n) :
    (clauses N t sources out).length ≤ 2*n+t*n*2^r+1 := by
  have h := inputClauses_length t sources
  simp only [clauses,List.length_append,List.length_map,N.acceptingClauses_length]
  omega

theorem clause_width (N : LocalNetwork n r) (t : ℕ) (sources : Fin n → InputSource p) (out : Fin n)
    (c : List (Variable p n t × Bool)) (hc : c ∈ clauses N t sources out) : c.length ≤ r+2 := by
  rcases List.mem_append.mp hc with hc | hc
  · exact (inputClause_width t sources c hc).trans (by omega)
  · obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    simpa only [List.length_map] using N.acceptingClause_width t out d hd
end InitialNetwork

lemma reindexCNF_clause_width {V : Type*} {n : ℕ} (e : V ≃ Fin n) (cs : RawCNF V) (W : ℕ)
    (h : ∀ c ∈ cs, c.length ≤ W) (i : Fin (cs.map (List.map (fun l => (e l.1,l.2)))).length) :
    ((reindexCNF e cs).clause i).length ≤ W := by
  have hm := List.get_mem (cs.map (List.map (fun l => (e l.1,l.2)))) i
  obtain ⟨c,hc,he⟩ := List.mem_map.mp hm
  change ((cs.map (List.map (fun l => (e l.1,l.2)))).get i).length ≤ W
  rw [← he,List.length_map]
  exact h c hc

namespace VerifierTableau
open TM2BooleanEncoding
variable {v : BitString → Bool}
variable (M : Turing.TM2ComputableInPolyTime id Computability.encodeBool v)

theorem positiveFormula_width (x : BitString) (m : ℕ) (ht : HasTrueSymbol M)
    (i : Fin ((InitialNetwork.clauses (network M.tm (height M x m)) (horizon M x m)
      (sources M x m) (outputWire M x m ht)).map
      (List.map (fun l => ((InitialNetwork.variableEquiv m (bitCount M.tm (height M x m))
        (horizon M x m)) l.1,l.2)))).length) :
    ((positiveFormula M x m ht).clause i).length ≤ Fintype.card (Port M.tm)+2 := by
  apply reindexCNF_clause_width
  exact InitialNetwork.clause_width _ _ _ _

/-- Actual byte-level encoding size of the concrete machine-to-CNF construction.
Its factors are explicit and polynomial in certificate length, input length,
height and time; the local exponential is a machine-only constant. -/
theorem positiveFormula_bits (x : BitString) (m : ℕ) (ht : HasTrueSymbol M) :
    (positiveFormula M x m ht).bits.length ≤
      10*(m+(horizon M x m+1)*bitCount M.tm (height M x m)+1)*(Fintype.card (Port M.tm)+3)*
        (2*bitCount M.tm (height M x m)+horizon M x m*bitCount M.tm (height M x m)*
          2^Fintype.card (Port M.tm)+2) := by
  have hb := CNF.bits_length_le (positiveFormula M x m ht) (Fintype.card (Port M.tm)+2)
    (positiveFormula_width M x m ht)
  have hc := InitialNetwork.clauses_length (network M.tm (height M x m)) (horizon M x m)
    (sources M x m) (outputWire M x m ht)
  apply hb.trans
  apply Nat.mul_le_mul_left
  simpa only [List.length_map] using Nat.add_le_add_right hc 1

end VerifierTableau
end HiddenCircuits.Complexity
