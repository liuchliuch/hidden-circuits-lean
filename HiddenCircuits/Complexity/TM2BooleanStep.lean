import HiddenCircuits.Complexity.OneHot

/-! A constructive Boolean implementation of one actual TM2 macrostep: decode a
fixed-size control/prefix snapshot, compute the bounded effect, and select the
needed shifted input slot. No whole-configuration truth table is used. -/
namespace HiddenCircuits.Complexity.TM2BooleanEncoding
open Turing.TM2
attribute [local instance] Classical.propDecidable

noncomputable def inspectionConstant (M : Turing.FinTM2) : ℕ := by
  letI := M.ΛFin
  exact ∑ q : M.Λ, TM2Locality.inspectionBudget (M.m q)

lemma statement_inspection_le (M : Turing.FinTM2) (q : M.Λ) :
    TM2Locality.inspectionBudget (M.m q) ≤ inspectionConstant M := by
  letI := M.ΛFin
  change _ ≤ ∑ q : M.Λ, TM2Locality.inspectionBudget (M.m q)
  exact Finset.single_le_sum (f := fun q : M.Λ => TM2Locality.inspectionBudget (M.m q))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)

noncomputable def snapshot (M : Turing.FinTM2) (height : ℕ) (w : Cell M height → Bool)
    (k : M.K) : List (M.Γ k) := decodePrefix M height (2*inspectionConstant M) w k

lemma snapshot_agrees (M : Turing.FinTM2) (height : ℕ) (c : M.Cfg) (hc : Valid M height c)
    (q : M.Λ) : TM2Locality.Agree (2*TM2Locality.inspectionBudget (M.m q)) c.stk
      (snapshot M height (encode M height c)) := by
  intro k
  rw [snapshot,decodePrefix_encode M height _ c hc]
  rw [List.take_take,Nat.min_eq_left (Nat.mul_le_mul_left 2 (statement_inspection_le M q))]

noncomputable def computedControl (M : Turing.FinTM2) (height : ℕ)
    (w : Cell M height → Bool) : Control M :=
  match decodeControl M height w with
  | (none,v) => (none,v)
  | (some q,v) =>
    let c := stepAux (M.m q) v (snapshot M height w)
    (c.l,c.var)

noncomputable def computedEffects (M : Turing.FinTM2) (height : ℕ)
    (w : Cell M height → Bool) : TM2Effects.Effects (Γ := M.Γ) :=
  match decodeControl M height w with
  | (none,_) => fun _ => StackEffect.identity
  | (some q,v) => TM2Effects.effectsOf (M.m q) v (snapshot M height w)

def actualEffects (M : Turing.FinTM2) (c : M.Cfg) : TM2Effects.Effects (Γ := M.Γ) :=
  match c.l with
  | none => fun _ => StackEffect.identity
  | some q => TM2Effects.effectsOf (M.m q) c.var c.stk

lemma stutter_none (M : Turing.FinTM2) (c : M.Cfg) (h : c.l = none) : stutter M.step c = c := by
  rcases c with ⟨l,v,S⟩
  dsimp at h
  subst l
  rfl

lemma stutter_some (M : Turing.FinTM2) (c : M.Cfg) (q : M.Λ) (h : c.l = some q) :
    stutter M.step c = stepAux (M.m q) c.var c.stk := by
  rcases c with ⟨l,v,S⟩
  dsimp at h
  subst l
  rfl

theorem computedControl_encode (M : Turing.FinTM2) (height : ℕ) (c : M.Cfg)
    (hc : Valid M height c) : computedControl M height (encode M height c) =
      ((stutter M.step c).l,(stutter M.step c).var) := by
  unfold computedControl
  rw [decodeControl_encode]
  cases h : c.l with
  | none => rw [stutter_none M c h]; exact Prod.ext h.symm rfl
  | some q =>
    rw [stutter_some M c q h]
    have hp := snapshot_agrees M height c hc q
    have hb : TM2Locality.Agree (TM2Locality.inspectionBudget (M.m q)) c.stk
        (snapshot M height (encode M height c)) := TM2Locality.agree_mono hp (by omega)
    have he := TM2Locality.control_local (M.m q) c.var c.stk _ hb
    exact (Prod.ext he.1 he.2).symm

theorem computedEffects_encode (M : Turing.FinTM2) (height : ℕ) (c : M.Cfg)
    (hc : Valid M height c) : computedEffects M height (encode M height c) = actualEffects M c := by
  unfold computedEffects actualEffects
  rw [decodeControl_encode]
  cases h : c.l with
  | none => rfl
  | some q => exact (TM2Effects.effectsOf_local (M.m q) c.var c.stk _ (snapshot_agrees M height c hc q)).symm

lemma actualEffects_apply (M : Turing.FinTM2) (c : M.Cfg) (k : M.K) :
    (actualEffects M c k).apply (c.stk k) = (stutter M.step c).stk k := by
  unfold actualEffects
  cases h : c.l with
  | none => rw [stutter_none M c h]; exact StackEffect.identity_apply _
  | some q => rw [stutter_some M c q h]; exact TM2Effects.effectsOf_apply _ _ _ _

noncomputable def nextSymbol (M : Turing.FinTM2) (height : ℕ) (w : Cell M height → Bool)
    (k : M.K) (j : ℕ) : Option (M.Γ k) :=
  let e := computedEffects M height w k
  if j < e.inserted.length then e.inserted[j]?
  else (decodeSlot M height w k (j-e.inserted.length+e.removed)).map Subtype.val

theorem nextSymbol_encode (M : Turing.FinTM2) (height : ℕ) (c : M.Cfg)
    (hc : Valid M height c) (k : M.K) (j : ℕ) :
    nextSymbol M height (encode M height c) k j = ((stutter M.step c).stk k)[j]? := by
  unfold nextSymbol
  rw [computedEffects_encode M height c hc]
  simp_rw [decodeSlot_encode M height c hc]
  rw [← actualEffects_apply M c k]
  exact (StackEffect.getElem?_apply _ _ _).symm

noncomputable def stepCode (M : Turing.FinTM2) (height : ℕ)
    (w : Cell M height → Bool) : Cell M height → Bool := by
  classical
  exact fun cell => match cell with
    | .inl q => decide (computedControl M height w = q)
    | .inr ⟨k,(i,a)⟩ => decide (nextSymbol M height w k i.val = a.map Subtype.val)

/-- A real Boolean transition implementation, correct for the actual encoded
machine states. Output height validity is supplied by the global tableau bound. -/
theorem stepCode_encode (M : Turing.FinTM2) (height : ℕ) (c : M.Cfg) (hc : Valid M height c) :
    stepCode M height (encode M height c) = encode M height (stutter M.step c) := by
  classical
  funext cell
  cases cell with
  | inl q => simp only [stepCode,encode,computedControl_encode M height c hc]
  | inr cell =>
    rcases cell with ⟨k,i,a⟩
    simp only [stepCode,encode,nextSymbol_encode M height c hc]

end HiddenCircuits.Complexity.TM2BooleanEncoding
