import HiddenCircuits.Complexity.TM2BooleanStep

/-! A fixed finite port set for every Boolean output cell. Its width depends only
on the verifier, while the port addresses use elementary bounded shifts. -/
namespace HiddenCircuits.Complexity.TM2BooleanEncoding
attribute [local instance] Classical.propDecidable

abbrev Position (M : Turing.FinTM2) :=
  Fin (2*inspectionConstant M) ⊕ (Fin (inspectionConstant M+1) × Fin (inspectionConstant M+1))
abbrev Port (M : Turing.FinTM2) :=
  Control M ⊕ ((k : M.K) × (Position M × Option (Symbol M k)))

noncomputable instance portFintype (M : Turing.FinTM2) : Fintype (Port M) := by
  letI := M.kFin
  infer_instance

def portPosition (M : Turing.FinTM2) (j : ℕ) : Position M → ℕ
  | .inl i => i.val
  | .inr (a,b) => j-a.val+b.val

/-- Out-of-range ports are mapped to a fixed dummy control cell. Their values are
ignored by the decoder, which supplies the empty marker directly. -/
def portCell (M : Turing.FinTM2) (height j : ℕ) : Port M → Cell M height
  | .inl q => .inl q
  | .inr ⟨k,(p,a)⟩ =>
    if h : portPosition M j p < height then .inr ⟨k,(⟨portPosition M j p,h⟩,a)⟩
    else .inl (none,M.initialState)

def PortAgree (M : Turing.FinTM2) (height j : ℕ) (w z : Cell M height → Bool) : Prop :=
  ∀ p, w (portCell M height j p) = z (portCell M height j p)

lemma decodeControl_eq_of_ports (M : Turing.FinTM2) (height j : ℕ) {w z : Cell M height → Bool}
    (h : PortAgree M height j w z) : decodeControl M height w = decodeControl M height z := by
  have he : (fun q : Control M => w (Sum.inl q)) = (fun q => z (Sum.inl q)) :=
    funext (fun q => h (Sum.inl q))
  unfold decodeControl
  rw [he]

lemma decodeSlot_eq_of_ports (M : Turing.FinTM2) (height j : ℕ) {w z : Cell M height → Bool}
    (h : PortAgree M height j w z) (k : M.K) (p : Position M) :
    decodeSlot M height w k (portPosition M j p) = decodeSlot M height z k (portPosition M j p) := by
  unfold decodeSlot
  split_ifs with hp
  · have he : (fun a : Option (Symbol M k) => w (Sum.inr ⟨k,(⟨portPosition M j p,hp⟩,a)⟩)) =
        (fun a => z (Sum.inr ⟨k,(⟨portPosition M j p,hp⟩,a)⟩)) := by
      funext a
      simpa [portCell,hp] using h (Sum.inr ⟨k,(p,a)⟩)
    rw [he]
  · rfl

lemma snapshot_eq_of_ports (M : Turing.FinTM2) (height j : ℕ) {w z : Cell M height → Bool}
    (h : PortAgree M height j w z) : snapshot M height w = snapshot M height z := by
  funext k
  unfold snapshot decodePrefix
  apply congrArg (List.filterMap id)
  apply congrArg List.ofFn
  funext i
  rw [show decodeSlot M height w k i.val = decodeSlot M height z k i.val from
    decodeSlot_eq_of_ports M height j h k (Sum.inl i)]

lemma computedControl_eq_of_ports (M : Turing.FinTM2) (height j : ℕ) {w z : Cell M height → Bool}
    (h : PortAgree M height j w z) : computedControl M height w = computedControl M height z := by
  unfold computedControl
  rw [decodeControl_eq_of_ports M height j h,snapshot_eq_of_ports M height j h]

lemma computedEffects_eq_of_ports (M : Turing.FinTM2) (height j : ℕ) {w z : Cell M height → Bool}
    (h : PortAgree M height j w z) : computedEffects M height w = computedEffects M height z := by
  unfold computedEffects
  rw [decodeControl_eq_of_ports M height j h,snapshot_eq_of_ports M height j h]

lemma computedEffects_cost (M : Turing.FinTM2) (height : ℕ) (w : Cell M height → Bool) (k : M.K) :
    (computedEffects M height w k).cost ≤ inspectionConstant M := by
  unfold computedEffects
  cases he : decodeControl M height w with
  | mk q v =>
    cases q with
    | none => simp
    | some q => exact (TM2Effects.effectsOf_cost _ _ _ _).trans (statement_inspection_le M q)

lemma nextSymbol_eq_of_ports (M : Turing.FinTM2) (height j : ℕ) {w z : Cell M height → Bool}
    (h : PortAgree M height j w z) (k : M.K) : nextSymbol M height w k j = nextSymbol M height z k j := by
  unfold nextSymbol
  rw [computedEffects_eq_of_ports M height j h]
  dsimp only
  split_ifs with hj
  · rfl
  · have hc := computedEffects_cost M height z k
    unfold StackEffect.cost at hc
    have he := decodeSlot_eq_of_ports M height j h k
      (Sum.inr (⟨(computedEffects M height z k).inserted.length,by omega⟩,
        ⟨(computedEffects M height z k).removed,by omega⟩))
    exact congrArg (Option.map Subtype.val) he

def cellIndex (M : Turing.FinTM2) {height : ℕ} : Cell M height → ℕ
  | .inl _ => 0
  | .inr ⟨_,(i,_)⟩ => i.val

/-- The entire Boolean transition has a proved, input-length-independent local width. -/
theorem stepCode_depends_ports (M : Turing.FinTM2) (height : ℕ) (cell : Cell M height)
    {w z : Cell M height → Bool} (h : PortAgree M height (cellIndex M cell) w z) :
    stepCode M height w cell = stepCode M height z cell := by
  classical
  cases cell with
  | inl q =>
    change decide (computedControl M height w = q) = decide (computedControl M height z = q)
    rw [computedControl_eq_of_ports M height 0 h]
  | inr cell =>
    rcases cell with ⟨k,i,a⟩
    change decide (nextSymbol M height w k i.val = a.map Subtype.val) =
      decide (nextSymbol M height z k i.val = a.map Subtype.val)
    rw [nextSymbol_eq_of_ports M height i.val h k]

/-- The exact width is a verifier constant. -/
theorem port_card (M : Turing.FinTM2) :
    Fintype.card (Port M) = controlBits M+
      (2*inspectionConstant M+(inspectionConstant M+1)^2)*symbolBits M := by
  letI := M.kFin
  simp only [Port,Fintype.card_sum,Fintype.card_sigma,Fintype.card_prod,Fintype.card_option,
    Position,Fintype.card_fin,controlBits,symbolBits,Finset.mul_sum,pow_two]

end HiddenCircuits.Complexity.TM2BooleanEncoding
