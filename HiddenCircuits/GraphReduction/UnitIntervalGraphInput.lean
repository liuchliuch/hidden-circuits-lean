import HiddenCircuits.GraphReduction.UnitIntervalExtraction
import HiddenCircuits.GraphReduction.Runtime.CoordinateGraphDefs
import HiddenCircuits.Complexity.EncodingSoundness

/-! The ordinary binary-graph frontend and literal bounded-grid payload.
These definitions are executable and have exact output semantics and polynomial
output size. A finite binary-machine execution theorem is a separate obligation. -/
namespace HiddenCircuits.GraphReduction.UnitIntervalGraphInput
open Complexity Complexity.BinaryArithmetic UnitIntervalExtraction

def asIntegerInput (G : GraphInput) (r : GridRepresentation G.2.graph) : UnitIntegerRepresentation G where
  denominator := UnitInterval.RationalGrid.denominator (V:=Fin G.1)
  positive := by exact_mod_cast UnitInterval.RationalGrid.denominator_pos (V:=Fin G.1)
  left v := r.left v
  adjacency i j := by
    rw [r.adjacency,Runtime.CoordinateGraph.integer_intervals]
    · apply and_congr_right
      intro _
      constructor
      · rintro ⟨hi,hj⟩; constructor <;> omega
      · rintro ⟨hi,hj⟩; constructor <;> omega
    · exact_mod_cast UnitInterval.RationalGrid.denominator_pos (V:=Fin G.1)

/-- Malformed graph bytes and recognition rejects both give `none`. -/
def gridBytes (xs : BitString) : Option BitString := do
  let G ← GraphInput.decode xs
  let r ← extract G.2.graph
  pure (unitCoordinateBits G (asIntegerInput G r))

/-- The native-coordinate parser reconstructs exactly the same labeled graph. -/
theorem roundtrip (G : GraphInput) (r : GridRepresentation G.2.graph) :
    Runtime.CoordinateGraph.bits (unitCoordinateBits G (asIntegerInput G r)) = G.encode :=
  Runtime.CoordinateGraph.bits_representation G (asIntegerInput G r)

lemma signed_nat_length (n : ℕ) : (signedBits (n : ℤ)).length ≤ n+1 := by
  simp only [signedBits,List.length_cons,Int.natAbs_natCast,encodeNat_length]
  exact Nat.add_le_add_right (Nat.size_le.mpr Nat.lt_two_pow_self) 1

lemma word_length_bound (G : GraphInput) (r : GridRepresentation G.2.graph)
    (w : BitString) (hw : w ∈ signedBits (asIntegerInput G r).denominator ::
      List.ofFn (fun v => signedBits ((asIntegerInput G r).left v))) :
    w.length ≤ 2*(G.1+1)^2+1 := by
  have hd : UnitInterval.RationalGrid.denominator (V:=Fin G.1) ≤ G.1+1 := by
    simp only [UnitInterval.RationalGrid.denominator,Fintype.card_fin]
    omega
  rcases List.mem_cons.mp hw with rfl|hw
  · exact (signed_nat_length _).trans (by nlinarith)
  · obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hw
    have hv := r.bound v
    simp only [Fintype.card_fin] at hv
    exact (signed_nat_length _).trans (by nlinarith)

lemma encode_list_bound (words : List BitString) (B : ℕ) (h : ∀ w ∈ words, w.length ≤ B) :
    (encodeBitList words).length ≤ words.length*(2*B+2) := by
  induction words with
  | nil => simp [encodeBitList]
  | cons w ws ih =>
    have hw := h w (by simp)
    have ht := ih (fun v hv => h v (by simp [hv]))
    simp only [encodeBitList,List.length_cons,pairBits_length] at *
    nlinarith

/-- A deliberately coarse cubic bit-length bound; this is an output-size
bound and does not substitute for runtime accounting. -/
theorem grid_bits_length (G : GraphInput) (r : GridRepresentation G.2.graph) :
    (unitCoordinateBits G (asIntegerInput G r)).length ≤
      (G.1+1)*(4*(G.1+1)^2+4) := by
  have h := encode_list_bound
    (signedBits (asIntegerInput G r).denominator :: List.ofFn (fun v => signedBits ((asIntegerInput G r).left v)))
    (2*(G.1+1)^2+1) (word_length_bound G r)
  simp only [List.length_cons,List.length_ofFn] at h
  change (encodeBitList _).length ≤ _
  nlinarith

theorem gridBytes_encode_isSome (G : GraphInput) :
    (gridBytes G.encode).isSome = true ↔ RealUnitInterval.UnitIntervalGraph G.2.graph := by
  simp only [gridBytes,GraphInput.decode_encode,Option.bind_some]
  cases he : extract G.2.graph with
  | none => simpa [he] using extract_iff G.2.graph
  | some r => simpa [he] using extract_iff G.2.graph

theorem gridBytes_size {xs ys : BitString} (h : gridBytes xs = some ys) :
    ys.length ≤ (xs.length+1)*(4*(xs.length+1)^2+4) := by
  cases hd : GraphInput.decode xs with
  | none => simp [gridBytes,hd] at h
  | some G =>
    cases hr : extract G.2.graph with
    | none => simp [gridBytes,hd,hr] at h
    | some r =>
      have hy : unitCoordinateBits G (asIntegerInput G r) = ys := by
        simpa [gridBytes,hd,hr] using h
      subst ys
      have hn := GraphInput.decode_vertices_bound hd
      exact (grid_bits_length G r).trans (by gcongr)

end HiddenCircuits.GraphReduction.UnitIntervalGraphInput
