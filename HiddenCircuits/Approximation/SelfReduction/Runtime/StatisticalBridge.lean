import HiddenCircuits.Approximation.SelfReduction.Runtime.MatchTallyLoop
import HiddenCircuits.Approximation.SelfReduction.Runtime.RobustSelect

/-! Pointwise connection between the actual tally/boost machines and the exact
functions used in the finite concentration proof. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity

theorem repeatCount_eq (k : ℕ) : 2*k+1+1=2*(k+1) := by omega

/-- Failure differs from every partner, including partner zero. -/
def encodePartner {b : ℕ} : Option (Fin (b+1)) → BitString
  | none => []
  | some i => true::List.replicate i.val true

 theorem encodePartner_injective (b : ℕ) : Function.Injective (@encodePartner b) := by
  intro x y h
  cases x with
  | none => cases y <;> simp_all [encodePartner]
  | some i =>
    cases y with
    | none => simp [encodePartner] at h
    | some j =>
      apply congrArg some
      apply Fin.ext
      have he := congrArg List.length h
      simpa [encodePartner] using he

 theorem encodePartner_length {b : ℕ} (x : Option (Fin (b+1))) : (encodePartner x).length ≤ b+1 := by
  cases x with
  | none => simp [encodePartner]
  | some i => simp [encodePartner]; omega

/-- Actual sample-word tally is exactly the event count in `eventFrequency`. -/
theorem sampled_partner_tally {α : Type*} (b n : ℕ) (sample : α → Option (Fin (b+1)))
    (r : Fin n → α) (i : Fin (b+1)) (g : BitString → ℕ) :
    ∃ t, occurrenceTally.Executes g
      (matchStore (encodePartner (some i)) (encodeBitList (List.ofFn (fun j => encodePartner (sample (r j))))) 0 [] [] [])
      (matchStore (encodePartner (some i)) [] (eventCount n (fun a => sample a=some i) r) [] [] []) t ∧
      t ≤ 1+n*(60*(2*b+3)) := by
  obtain ⟨t,ht,hb⟩ := occurrenceTally_ofFn g n (b+1) (fun j => encodePartner (sample (r j)))
    (fun j => encodePartner_length _) (encodePartner (some i))
  have he : (Finset.univ.filter (fun j => encodePartner (some i)=encodePartner (sample (r j)))).card =
      eventCount n (fun a => sample a=some i) r := by
    unfold eventCount
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ((encodePartner_injective b) h).symm,fun h => congrArg encodePartner h.symm⟩
  rw [he] at ht
  refine ⟨t,ht,?_⟩
  have hi : (encodePartner (some i)).length ≤ b+1 := encodePartner_length (b := b) (some i)
  have hin : b+1+(encodePartner (some i)).length+1 ≤ 2*b+3 := by omega
  have hprod : n*(60*(b+1+(encodePartner (some i)).length+1)) ≤ n*(60*(2*b+3)) :=
    Nat.mul_le_mul_left n (Nat.mul_le_mul_left 60 hin)
  exact hb.trans (Nat.add_le_add_left hprod 1)

/-- An entire confidence booster is executed by the proved finite machine,
with exact correspondence on every input tape, not just on successful events. -/
theorem amplified_count_machine {α : Type*} (E : α → Prop) [DecidablePred E]
    (T k : ℕ) (r : StageTape α T k) (g : BitString → ℕ) :
    let c : Fin (2*k+1+1) → ℕ := fun i => eventCount (batchSize T) E (r (Fin.cast (repeatCount_eq k) i))
    ∃ t, robustSelect.Executes g
      (robustStore 0 (8*T) 0 [] (unaryValues (List.ofFn c)) [] [])
      (robustStore (naturalAmplifiedCount E T k r) 0 0 [] [] [] []) t ∧
      t ≤ 2000*(2*k+3)^2*(batchSize T+8*T+1)+200 := by
  dsimp only
  have hq (i : Fin ((2 : ℕ)*k+1+1)) : eventCount (batchSize T) E (r (Fin.cast (repeatCount_eq k) i)) ≤ batchSize T := by
    unfold eventCount
    exact (Finset.card_filter_le (Finset.univ : Finset (Fin (batchSize T)))
      (fun j => E (r (Fin.cast (repeatCount_eq k) i) j))).trans_eq
        ((Finset.card_univ).trans (Fintype.card_fin (batchSize T)))
  obtain ⟨t,ht,hb⟩ := robustSelect_executes g (2*k+1) (8*T) (batchSize T)
    (fun i => eventCount (batchSize T) E (r (Fin.cast (repeatCount_eq k) i))) hq
  refine ⟨t,ht,?_⟩
  convert hb using 1 <;> congr 2 <;> omega

end HiddenCircuits.Approximation.SelfReduction.Runtime
