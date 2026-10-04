import HiddenCircuits.Approximation.CanonicalPaths.UnionCode
import HiddenCircuits.Approximation.CanonicalPaths.CyclePhases
import HiddenCircuits.Approximation.CanonicalPaths.CompanionRoutes
namespace HiddenCircuits.Approximation.CanonicalPaths.TrafficEncoding
open LocalRoutes UnionReconstruction
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {R : Fin n → Fin n → Prop}
abbrev Pairs (z : State R) (d : ℕ) :=
  {pq : State R × State R // ∃ active : Fin n,
    Interrupted pq.1.val pq.2.val z.val active ∧ HasCompanion pq.1 pq.2 z d}
noncomputable def active {z : State R} {d : ℕ} (t : Pairs z d) : Fin n := t.property.choose
theorem interrupted {z : State R} {d : ℕ} (t : Pairs z d) :
    Interrupted t.val.1.val t.val.2.val z.val (active t) := t.property.choose_spec.1
noncomputable def companion {z : State R} {d : ℕ} (t : Pairs z d) : State R :=
  t.property.choose_spec.2.choose
noncomputable def exceptional {z : State R} {d : ℕ} (t : Pairs z d) : Finset (Fin n) :=
  t.property.choose_spec.2.choose_spec.choose
theorem exceptional_card {z : State R} {d : ℕ} (t : Pairs z d) : (exceptional t).card ≤ d :=
  t.property.choose_spec.2.choose_spec.choose_spec.1
theorem outside {z : State R} {d : ℕ} (t : Pairs z d) :
    ∀ i, i∉exceptional t → ({t.val.1.val i,t.val.2.val i} : Set (Fin n))=
      {z.val i,(companion t).val i} := by
  intro i hi
  have h := t.property.choose_spec.2.choose_spec.choose_spec.2 i hi
  have hh := congrArg (fun f : Finset (Fin n) => (f : Set (Fin n))) h.symm
  simpa only [Finset.coe_pair] using hh
noncomputable def encode (fallback : Fin n) {z : State R} {d : ℕ} (t : Pairs z d) :
    State R × RepairCode n d × Fin n × Fin n :=
  (companion t,encodeRepair fallback t.val.1.val t.val.2.val (exceptional t) (exceptional_card t),
    active t,t.val.1.val (active t))
theorem encode_injective (fallback : Fin n) (z : State R) (d : ℕ) :
    Function.Injective (encode fallback : Pairs z d → State R × RepairCode n d × Fin n × Fin n) := by
  intro x y h
  have hw : companion x=companion y := congrArg (fun t : State R × RepairCode n d × Fin n × Fin n => t.1) h
  have hc : encodeRepair fallback x.val.1.val x.val.2.val (exceptional x) (exceptional_card x)=
      encodeRepair fallback y.val.1.val y.val.2.val (exceptional y) (exceptional_card y) :=
    congrArg (fun t : State R × RepairCode n d × Fin n × Fin n => t.2.1) h
  have ha : active x=active y := congrArg (fun t : State R × RepairCode n d × Fin n × Fin n => t.2.2.1) h
  have ho : x.val.1.val (active x)=y.val.1.val (active y) :=
    congrArg (fun t : State R × RepairCode n d × Fin n × Fin n => t.2.2.2) h
  have hU : SameUnion x.val.1.val x.val.2.val y.val.1.val y.val.2.val :=
    sameUnion_of_equal_code fallback _ _ _ _ z.val (companion x).val
      (exceptional x) (exceptional y) (exceptional_card x) (exceptional_card y)
      (outside x) (by simpa only [hw] using outside y) hc
  have hy : Interrupted y.val.1.val y.val.2.val z.val (active x) := by
    simpa only [ha] using interrupted y
  have horient : y.val.1.val (active x)=x.val.1.val (active x) := by
    rw [← ha] at ho
    exact ho.symm
  have he := reconstruct_interrupted hU (interrupted x) hy horient
  apply Subtype.ext
  exact Prod.ext (Subtype.ext he.1) (Subtype.ext he.2)
theorem pairs_card_bound (z : State R) (d : ℕ) :
    Fintype.card (Pairs z d) ≤
      Fintype.card (State R)*((n+1)^d*n^d*n^d)*n*n := by
  classical
  by_cases hn : n=0
  · subst n
    haveI : IsEmpty (Pairs z d) := ⟨fun t => Fin.elim0 (active t)⟩
    simp
  · let fallback : Fin n := ⟨0,Nat.pos_of_ne_zero hn⟩
    have h := Fintype.card_le_of_injective (encode fallback : Pairs z d →
      State R × RepairCode n d × Fin n × Fin n) (encode_injective fallback z d)
    simpa only [Fintype.card_prod,Fintype.card_fin,RepairCode.card,mul_assoc] using h
end HiddenCircuits.Approximation.CanonicalPaths.TrafficEncoding
