import HiddenCircuits.Approximation.Initialization.RawExtraction
import HiddenCircuits.Approximation.SelfReduction.Runtime.CoinSlices

/-! The actual raw-list accumulator consumes exactly the finite
independent blocks analyzed by ForwardExtraction. Surplus tails are arbitrary. -/
namespace HiddenCircuits.Approximation.Initialization.RawExtraction
open Complexity SelfReduction SamplerRuntime

def blocks {d m : ℕ} (r : Fin d → CoinTape m) (tail : BitString) : BitString :=
  (List.ofFn (fun i => List.ofFn (r i))).flatten ++ tail

theorem blocks_split {d m : ℕ} (r : CoinTape (d*m)) :
    blocks (splitBlocks d m r) [] = List.ofFn r := by
  simp [blocks,SelfReduction.Runtime.ofFn_splitBlocks]

theorem blocks_cons {d m : ℕ} (r : Fin (d+1) → CoinTape m) (tail : BitString) :
    blocks r tail = List.ofFn (r 0) ++ blocks (fun i => r i.succ) tail := by
  simp [blocks,List.ofFn_succ,List.append_assoc]

theorem blocks_take {d m : ℕ} (r : Fin (d+1) → CoinTape m) (tail : BitString) :
    TapeRead.takePadded m (blocks r tail) = List.ofFn (r 0) := by
  rw [blocks_cons,TapeRead.prefix_eq_take _ _ (by simp)]
  simp

theorem blocks_drop {d m : ℕ} (r : Fin (d+1) → CoinTape m) (tail : BitString) :
    (blocks r tail).drop m = blocks (fun i => r i.succ) tail := by
  rw [blocks_cons]
  simp

theorem run_blocks {b : ℕ} (G : MatrixGraph (b+1)) (k d fuel : ℕ)
    (U : {U : Finset (Fin (b+1)) // U.card = 2*d})
    (r : Fin d → CoinTape (ResidualTest.bits b k)) (tail : BitString)
    (π : Equiv.Perm (Fin (b+1))) (hf : d ≤ fuel) :
    run G (b+1+k) fuel U.val (blocks r tail) π =
      ForwardExtraction.run G.graph k d ⟨d,some U⟩ r π := by
  induction d generalizing fuel π with
  | zero =>
    have hU : U.val = ∅ := Finset.card_eq_zero.mp (by simpa using U.property)
    simp [hU,ForwardExtraction.run,ForwardExtraction.leaf]
  | succ d ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hU : U.val.Nonempty := Finset.card_pos.mp (by rw [U.property]; omega)
      have hp : U.val.min' hU = (matchingPivot U).val := rfl
      have hlen : stageLength (b+1) (b+1+k) = ResidualTest.bits b k := rfl
      have hselect : (List.finRange (b+1)).find?
          (CandidateTest.test G U.val (b+1+k) (List.ofFn (r 0)) (U.val.min' hU)) =
          MatchingExtraction.select G.graph k ⟨d+1,some U⟩ (r 0) := by
        rw [hp]
        unfold MatchingExtraction.select
        congr 1
        funext v
        exact CandidateTest.test_child G U k (r 0) v
      rw [run,dif_pos hU,hlen,blocks_take,blocks_drop]
      dsimp only
      rw [hselect,ForwardExtraction.run]
      cases hs : MatchingExtraction.select G.graph k ⟨d+1,some U⟩ (r 0) with
      | none => rfl
      | some v =>
        have hc := MatchingExtraction.select_sound G.graph k ⟨d+1,some U⟩ (r 0) hs
        have ha : v ∈ U.val ∧ G.graph.Adj (matchingPivot U).val v := by
          by_contra h
          rw [matchingChild_active,dif_neg h] at hc
          exact Nat.lt_irrefl 0 hc
        let V : {U : Finset (Fin (b+1)) // U.card = 2*d} :=
          ⟨(U.val.erase (matchingPivot U).val).erase v,erased_card U v ha.1 ha.2.ne.symm⟩
        have he : matchingChild G.graph ⟨d+1,some U⟩ v = ⟨d,some V⟩ := by
          rw [matchingChild_active,dif_pos ha]
        dsimp only
        rw [he,hp]
        exact ih fuel V (fun i => r i.succ) _ (by omega)

end HiddenCircuits.Approximation.Initialization.RawExtraction
