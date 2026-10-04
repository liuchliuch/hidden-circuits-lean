import HiddenCircuits.Complexity.TM2BooleanEncoding

/-! Explicit finite one-hot decoders and exact finite-prefix reconstruction. -/
namespace HiddenCircuits.Complexity

def scanTrue {α : Type*} : List α → (α → Bool) → Option α
  | [], _ => none
  | a::as, w => if w a then some a else scanTrue as w

lemma scanTrue_unique {α : Type*} (as : List α) (w : α → Bool) (a : α)
    (ha : a ∈ as) (hwa : w a = true) (hu : ∀ b ∈ as, w b = true → b = a) :
    scanTrue as w = some a := by
  induction as with
  | nil => simp at ha
  | cons b bs ih =>
    by_cases hb : w b = true
    · have he := hu b (by simp) hb
      simp [scanTrue,he,hwa]
    · have ht : a ∈ bs := by
        rcases List.mem_cons.mp ha with he | ht
        · subst b; exact False.elim (hb hwa)
        · exact ht
      simpa [scanTrue,hb] using ih ht (fun c hc => hu c (List.mem_cons_of_mem _ hc))

noncomputable def decodeOneHot {α : Type*} [Fintype α] (w : α → Bool) : Option α :=
  scanTrue Finset.univ.toList w

/-- Decode an injectively represented symbol, rather than relying on an abstract
inverse or choosing an arbitrary satisfying value. -/
theorem decodeOneHot_image {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (a : α) :
    decodeOneHot (fun b => decide (f a = f b)) = some a := by
  apply scanTrue_unique
  · simp
  · simp
  · intro b _ h
    exact (hf (of_decide_eq_true h)).symm

/-- Padded optional slots reconstruct exactly the finite list prefix. -/
lemma optionalPrefix_filterMap {α : Type*} (l : List α) (r : ℕ) :
    ((List.ofFn (fun i : Fin r => l[i.val]?)).filterMap id) = l.take r := by
  induction r generalizing l with
  | zero => simp
  | succ r ih =>
    cases l with
    | nil => simp
    | cons a l => simpa [List.ofFn_succ] using congrArg (List.cons a) (ih l)

namespace TM2BooleanEncoding
attribute [local instance] Classical.propDecidable

noncomputable def decodeControl (M : Turing.FinTM2) (height : ℕ) (w : Cell M height → Bool) : Control M :=
  (decodeOneHot (fun q => w (Sum.inl q))).getD (some M.main,M.initialState)

@[simp] theorem decodeControl_encode (M : Turing.FinTM2) (height : ℕ) (c : M.Cfg) :
    decodeControl M height (encode M height c) = (c.l,c.var) := by
  classical
  unfold decodeControl
  have h := decodeOneHot_image (fun q : Control M => q) Function.injective_id (c.l,c.var)
  change (decodeOneHot (fun q => decide ((c.l,c.var) = q))).getD _ = _
  rw [h]
  rfl

noncomputable def decodeSlot (M : Turing.FinTM2) (height : ℕ) (w : Cell M height → Bool)
    (k : M.K) (j : ℕ) : Option (Symbol M k) :=
  if h : j < height then
    (decodeOneHot (fun a => w (Sum.inr ⟨k,(⟨j,h⟩,a)⟩))).getD none
  else none

/-- Every decoded slot of a valid encoded configuration is the original symbol
or its unique empty marker. -/
theorem decodeSlot_encode (M : Turing.FinTM2) (height : ℕ) (c : M.Cfg)
    (hc : Valid M height c) (k : M.K) (j : ℕ) :
    (decodeSlot M height (encode M height c) k j).map Subtype.val = (c.stk k)[j]? := by
  classical
  by_cases hj : j < height
  · obtain ⟨a,ha⟩ := stack_slot_exists M height c hc k ⟨j,hj⟩
    have hinj : Function.Injective (fun a : Option (Symbol M k) => a.map Subtype.val) :=
      Option.map_injective Subtype.val_injective
    have hd := decodeOneHot_image (fun a : Option (Symbol M k) => a.map Subtype.val) hinj a
    unfold decodeSlot
    rw [dif_pos hj]
    change ((decodeOneHot (fun b : Option (Symbol M k) =>
      decide ((c.stk k)[j]? = b.map Subtype.val))).getD none).map Subtype.val = _
    rw [ha,hd]
    rfl
  · simp only [decodeSlot,dif_neg hj,Option.map_none]
    exact (List.getElem?_eq_none (by have := hc.2 k;omega)).symm

noncomputable def decodePrefix (M : Turing.FinTM2) (height r : ℕ) (w : Cell M height → Bool)
    (k : M.K) : List (M.Γ k) :=
  (List.ofFn (fun i : Fin r => (decodeSlot M height w k i.val).map Subtype.val)).filterMap id

/-- The fixed-size transition snapshot is reconstructed faithfully from Boolean bits. -/
theorem decodePrefix_encode (M : Turing.FinTM2) (height r : ℕ) (c : M.Cfg)
    (hc : Valid M height c) (k : M.K) :
    decodePrefix M height r (encode M height c) k = (c.stk k).take r := by
  unfold decodePrefix
  simp_rw [decodeSlot_encode M height c hc]
  exact optionalPrefix_filterMap _ _

end TM2BooleanEncoding
end HiddenCircuits.Complexity
