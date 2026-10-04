import HiddenCircuits.Complexity.LocalNetworkCNF
import HiddenCircuits.Complexity.IntegerRecovery

/-! Reindex finite-variable clause lists into the actual CNF input type without
adding unused variables or changing assignment counts. -/
namespace HiddenCircuits.Complexity
open BoolCircuit
attribute [local instance] Classical.propDecidable

def finiteCNF {n : ℕ} (cs : RawCNF (Fin n)) : CNF n cs.length where
  clause k := cs.get k

theorem finiteCNF_satisfies {n : ℕ} (cs : RawCNF (Fin n)) (w : Fin n → Bool) :
    (finiteCNF cs).Satisfies w ↔ RawSatisfies cs w := by
  constructor
  · intro h c hc
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hc
    simpa only [← hi] using h i
  · intro h i
    exact h _ (List.get_mem _ _)

def reindexCNF {V : Type*} {n : ℕ} (e : V ≃ Fin n) (cs : RawCNF V) :
    CNF n (cs.map (List.map (fun l => (e l.1,l.2)))).length :=
  finiteCNF (cs.map (List.map (fun l => (e l.1,l.2))))

def reindexCNFEquiv {V : Type*} {n : ℕ} (e : V ≃ Fin n) (cs : RawCNF V) :
    {w : V → Bool // RawSatisfies cs w} ≃
    {v : Fin n → Bool // (reindexCNF e cs).Satisfies v} where
  toFun w := ⟨fun i => w.val (e.symm i),by
    rw [reindexCNF,finiteCNF_satisfies,rawSatisfies_map]
    simpa using w.property⟩
  invFun v := ⟨fun a => v.val (e a),by
    have h := (finiteCNF_satisfies _ v.val).mp v.property
    exact (rawSatisfies_map cs e v.val).mp h⟩
  left_inv w := by
    apply Subtype.ext
    funext a
    simp
  right_inv v := by
    apply Subtype.ext
    funext i
    simp

theorem reindexCNF_count {V : Type*} [Fintype V] {n : ℕ} (e : V ≃ Fin n) (cs : RawCNF V) :
    (reindexCNF e cs).satCount = Nat.card {w : V → Bool // RawSatisfies cs w} := by
  classical
  unfold CNF.satCount
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (reindexCNFEquiv e cs).symm

namespace LocalNetwork
variable {n r : ℕ} (N : LocalNetwork n r)

/-- The actual CNF instance for a bounded local computation, with a dense variable universe. -/
noncomputable def toCNF (t : ℕ) (out : Fin n) :=
  reindexCNF finProdFinEquiv (N.acceptingClauses t out)

/-- The finite clause input preserves the number of accepted initial assignments exactly. -/
theorem toCNF_count (t : ℕ) (out : Fin n) :
    (N.toCNF t out).satCount =
      Nat.card {input : Fin n → Bool // (N.step^[t] input) out = true} := by
  exact (reindexCNF_count finProdFinEquiv (N.acceptingClauses t out)).trans
    (N.accepting_count t out)

/-- Concrete exact recovery of bounded local-network acceptance by ordinary
independent-set queries; machine compilation remains a separate obligation. -/
theorem acceptance_from_independent_queries (t : ℕ) (out : Fin n) :
    recoverIntegerGrid ((t+1)*n)
      ((N.acceptingClauses t out).map (List.map (fun l => (finProdFinEquiv l.1,l.2)))).length
      (fun i j => (GraphInput.independentSetProblem
        ((N.toCNF t out).encodedCloneQuery i.val j.val) : ℤ)) =
      Nat.card {input : Fin n → Bool // (N.step^[t] input) out = true} := by
  rw [(N.toCNF t out).recoverIntegerGrid_encoded_correct]
  exact N.toCNF_count t out

end LocalNetwork
end HiddenCircuits.Complexity
