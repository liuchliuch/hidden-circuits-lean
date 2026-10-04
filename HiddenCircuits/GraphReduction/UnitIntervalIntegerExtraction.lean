import HiddenCircuits.GraphReduction.UnitIntervalMaskedRecognition
import HiddenCircuits.GraphReduction.UnitIntervalDyadicConstruction
import HiddenCircuits.GraphReduction.NatUnitIntervalGrid
import HiddenCircuits.GraphReduction.UnitIntervalExtraction

/-! Adjacency-only graph-to-grid extraction whose executable arithmetic is
entirely natural-number arithmetic: dyadic midpoint numerators, then division,
remainder, and comparison ranks. Real and rational values occur only in proofs. -/
namespace HiddenCircuits.GraphReduction.UnitIntervalIntegerExtraction
open UnitIntervalOrder UnitIntervalExtraction
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V} [DecidableRel G.Adj]

private lemma scaled_le {D a b : ℕ} (hD : 0 < D) :
    (a : ℚ)/D ≤ (b : ℚ)/D+1 ↔ a ≤ b+D := by
  have hp : (0 : ℚ) < D := by exact_mod_cast hD
  have he : (b : ℚ)/D+1 = ((b : ℚ)+D)/D := by
    rw [add_div,div_self hp.ne']
  rw [he,div_le_div_iff_of_pos_right hp]
  exact_mod_cast Iff.rfl

/-- Natural-only coordinate data from a checked, internally constructed order. -/
def fromOrder (ls : List V) (hn : ls.Nodup) (hc : ∀ v, v ∈ ls)
    (hu : ListUmbrella G ls) : GridRepresentation G := by
  let e := hn.getEquivOfForallMemList ls hc
  let u : V → ℕ := fun v => Dyadic.numerators ls.length (G.comap ls.get) (e.symm v)
  let D : ℕ := 2^ls.length
  have hD : 0 < D := by dsimp [D]; positivity
  refine { left := NatUnitIntervalGrid.numerator D u, adjacency := ?_, bound := ?_ }
  · intro v w
    let r := representationOfOrderedList ls hn hc hu
    have hleft : ∀ v, (u v : ℚ)/D = r.left v := by
      intro v
      exact Dyadic.numerators_refine ls.length (G.comap ls.get) hu (e.symm v)
    change G.Adj v w ↔ v ≠ w ∧
      NatUnitIntervalGrid.numerator D u v ≤ NatUnitIntervalGrid.numerator D u w+NatUnitIntervalGrid.denominator ∧
      NatUnitIntervalGrid.numerator D u w ≤ NatUnitIntervalGrid.numerator D u v+NatUnitIntervalGrid.denominator
    rw [NatUnitIntervalGrid.comparison D hD u v w,NatUnitIntervalGrid.comparison D hD u w v]
    rw [r.adjacency,UnitInterval.icc_overlap (by change r.left v ≤ r.left v+1; linarith)
      (by change r.left w ≤ r.left w+1; linarith)]
    change (v ≠ w ∧ r.left v ≤ r.left w+1 ∧ r.left w ≤ r.left v+1) ↔ _
    rw [←hleft v,←hleft w,scaled_le hD,scaled_le hD]
  · intro v
    exact NatUnitIntervalGrid.endpoint_bound D u v

/-- Graph input only. The entire executable path uses finite lists, masks, and
natural arithmetic, with no assumed recognition or representation certificate. -/
def extract (G : SimpleGraph V) [DecidableRel G.Adj] : Option (GridRepresentation G) :=
  match he : UnitIntervalMaskedRecognition.recognize G with
  | none => none
  | some ls =>
    let hs := UnitIntervalMaskedRecognition.search_sound G (Fintype.card V) Finset.univ ls he
    have hall : ∀ v, v ∈ ls := by
      intro v
      apply List.mem_toFinset.mp
      rw [hs.2.1]
      exact Finset.mem_univ v
    some (fromOrder ls hs.1 hall hs.2.2)

lemma extract_isSome (G : SimpleGraph V) [DecidableRel G.Adj] :
    (extract G).isSome = (UnitIntervalMaskedRecognition.recognize G).isSome := by
  unfold extract
  split <;> simp_all

theorem extract_iff (G : SimpleGraph V) [DecidableRel G.Adj] :
    (extract G).isSome = true ↔ RealUnitInterval.UnitIntervalGraph G := by
  rw [extract_isSome,UnitIntervalMaskedRecognition.recognize_iff]

end HiddenCircuits.GraphReduction.UnitIntervalIntegerExtraction
