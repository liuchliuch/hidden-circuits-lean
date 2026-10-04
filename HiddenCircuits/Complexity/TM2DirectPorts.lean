import HiddenCircuits.Complexity.TM2LocalNetwork

/-! A direct local rule for the uniform emitter. Unlike sparse completion, this
reads the named finite ports directly: the only variable-sized arithmetic is
bounded index shifting and boundary testing. All decoding/effect tables have
fixed verifier-dependent domains. -/
namespace HiddenCircuits.Complexity.TM2BooleanEncoding
open Turing.TM2
attribute [local instance] Classical.propDecidable

noncomputable def portControl (M : Turing.FinTM2) (a : Port M → Bool) : Control M :=
  (decodeOneHot (fun q => a (Sum.inl q))).getD (some M.main,M.initialState)

noncomputable def portSlot (M : Turing.FinTM2) (height j : ℕ) (a : Port M → Bool)
    (k : M.K) (p : Position M) : Option (Symbol M k) :=
  if portPosition M j p < height then
    (decodeOneHot (fun q => a (Sum.inr ⟨k,(p,q)⟩))).getD none
  else none

noncomputable def portSnapshot (M : Turing.FinTM2) (height : ℕ) (a : Port M → Bool)
    (k : M.K) : List (M.Γ k) :=
  (List.ofFn (fun i : Fin (2*inspectionConstant M) =>
    (portSlot M height 0 a k (Sum.inl i)).map Subtype.val)).filterMap id

lemma portControl_read (M : Turing.FinTM2) (height j : ℕ) (w : Cell M height → Bool) :
    portControl M (fun p => w (portCell M height j p)) = decodeControl M height w := rfl

lemma portSlot_read (M : Turing.FinTM2) (height j : ℕ) (w : Cell M height → Bool)
    (k : M.K) (p : Position M) :
    portSlot M height j (fun p => w (portCell M height j p)) k p =
      decodeSlot M height w k (portPosition M j p) := by
  unfold portSlot decodeSlot
  split_ifs with h
  · simp [portCell,h]
  · rfl

lemma portSnapshot_read (M : Turing.FinTM2) (height j : ℕ) (w : Cell M height → Bool) :
    portSnapshot M height (fun p => w (portCell M height j p)) = snapshot M height w := by
  funext k
  unfold portSnapshot snapshot decodePrefix
  congr 2
  funext i
  exact congrArg (Option.map Subtype.val) (portSlot_read M height j w k (Sum.inl i))

noncomputable def portComputedControl (M : Turing.FinTM2) (height : ℕ) (a : Port M → Bool) : Control M :=
  match portControl M a with
  | (none,v) => (none,v)
  | (some q,v) =>
    let c := stepAux (M.m q) v (portSnapshot M height a)
    (c.l,c.var)

noncomputable def portEffects (M : Turing.FinTM2) (height : ℕ) (a : Port M → Bool) :
    TM2Effects.Effects (Γ := M.Γ) :=
  match portControl M a with
  | (none,_) => fun _ => StackEffect.identity
  | (some q,v) => TM2Effects.effectsOf (M.m q) v (portSnapshot M height a)

lemma portComputedControl_read (M : Turing.FinTM2) (height j : ℕ) (w : Cell M height → Bool) :
    portComputedControl M height (fun p => w (portCell M height j p)) = computedControl M height w := by
  unfold portComputedControl computedControl
  rw [portControl_read,portSnapshot_read]
  rfl

lemma portEffects_read (M : Turing.FinTM2) (height j : ℕ) (w : Cell M height → Bool) :
    portEffects M height (fun p => w (portCell M height j p)) = computedEffects M height w := by
  unfold portEffects computedEffects
  rw [portControl_read,portSnapshot_read]
  rfl

lemma portEffects_cost (M : Turing.FinTM2) (height : ℕ) (a : Port M → Bool) (k : M.K) :
    (portEffects M height a k).cost ≤ inspectionConstant M := by
  unfold portEffects
  cases he : portControl M a with
  | mk q v =>
    cases q with
    | none => simp
    | some q => exact (TM2Effects.effectsOf_cost _ _ _ _).trans (statement_inspection_le M q)

noncomputable def effectPort (M : Turing.FinTM2) (height : ℕ) (a : Port M → Bool) (k : M.K) : Position M :=
  let e := portEffects M height a k
  let hc := portEffects_cost M height a k
  Sum.inr (⟨e.inserted.length,by dsimp [e];have := hc;unfold StackEffect.cost at this;omega⟩,
    ⟨e.removed,by dsimp [e];have := hc;unfold StackEffect.cost at this;omega⟩)

noncomputable def directRule (M : Turing.FinTM2) (height : ℕ) (cell : Cell M height) (a : Port M → Bool) : Bool :=
  match cell with
  | .inl q => decide (portComputedControl M height a = q)
  | .inr ⟨k,(i,s)⟩ =>
    let e := portEffects M height a k
    if i.val < e.inserted.length then decide (e.inserted[i.val]? = s.map Subtype.val)
    else decide ((portSlot M height i.val a k (effectPort M height a k)).map Subtype.val = s.map Subtype.val)

/-- Direct port evaluation is exactly the real Boolean TM2 transition on every
input bit assignment, not only on valid one-hot configurations. -/
theorem directRule_read (M : Turing.FinTM2) (height : ℕ) (cell : Cell M height) (w : Cell M height → Bool) :
    directRule M height cell (fun p => w (portCell M height (cellIndex M cell) p)) = stepCode M height w cell := by
  cases cell with
  | inl q =>
    simp only [directRule,stepCode,cellIndex,portComputedControl_read]
  | inr cell =>
    rcases cell with ⟨k,i,s⟩
    simp only [directRule,stepCode,cellIndex,portEffects_read]
    simp only [nextSymbol]
    split_ifs with h
    · simp [h]
    · simp only [portSlot_read,effectPort,portPosition,portEffects_read,h,if_false]

noncomputable def directNetwork (M : Turing.FinTM2) (height : ℕ) :
    LocalNetwork (bitCount M height) (Fintype.card (Port M)) where
  ports := encodedPorts M height
  rule i a := directRule M height ((cellEnumeration M height).symm i) (fun p => a (portEnumeration M p))

theorem directNetwork_step (M : Turing.FinTM2) (height : ℕ) (w : Fin (bitCount M height) → Bool) :
    (directNetwork M height).step w = encodedStep M height w := by
  funext i
  unfold LocalNetwork.step directNetwork encodedStep
  have h := directRule_read M height ((cellEnumeration M height).symm i)
    (fun c => w (cellEnumeration M height c))
  simpa [encodedPorts] using h

theorem directNetwork_step_eq (M : Turing.FinTM2) (height : ℕ) :
    (directNetwork M height).step = (network M height).step := by
  funext w
  rw [directNetwork_step,network_step]

/-- The prefix-height truncation is bounded by a fixed verifier constant. -/
theorem portSnapshot_cap (M : Turing.FinTM2) (height : ℕ) (a : Port M → Bool) :
    portSnapshot M height a = portSnapshot M (min height (2*inspectionConstant M)) a := by
  funext k
  unfold portSnapshot
  congr 2
  funext i
  unfold portSlot
  simp only [portPosition]
  have h : i.val < height ↔ i.val < min height (2*inspectionConstant M) := by
    have := i.isLt;omega
  simp only [h]

theorem portEffects_cap (M : Turing.FinTM2) (height : ℕ) (a : Port M → Bool) :
    portEffects M height a = portEffects M (min height (2*inspectionConstant M)) a := by
  unfold portEffects
  rw [portSnapshot_cap M height a]

end HiddenCircuits.Complexity.TM2BooleanEncoding
