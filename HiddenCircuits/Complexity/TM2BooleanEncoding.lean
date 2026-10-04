import HiddenCircuits.Complexity.StackEffects

/-! A faithful one-hot Boolean representation of the bounded actual TM2
configurations. Its number of bits is linear in the stack-height bound. -/
namespace HiddenCircuits.Complexity.TM2BooleanEncoding
attribute [local instance] Classical.propDecidable

abbrev Symbol (M : Turing.FinTM2) (k : M.K) :=
  {a : M.Γ k // (⟨k,a⟩ : (j : M.K) × M.Γ j) ∈ TM2Alphabet.alphabet M}

noncomputable instance symbolFintype (M : Turing.FinTM2) (k : M.K) : Fintype (Symbol M k) := by
  classical
  apply Fintype.ofInjective
    (fun a : Symbol M k => (⟨⟨k,a.val⟩,a.property⟩ : TM2Alphabet.alphabet M))
  intro a b h
  apply Subtype.ext
  have he := congrArg Subtype.val h
  simpa using he

abbrev Control (M : Turing.FinTM2) := Option M.Λ × M.σ

/-- One control bit for each finite control state, and one symbol bit for each
stack/position/possible symbol (including the empty marker). -/
abbrev Cell (M : Turing.FinTM2) (height : ℕ) :=
  Control M ⊕ ((k : M.K) × (Fin height × Option (Symbol M k)))

noncomputable instance controlFintype (M : Turing.FinTM2) : Fintype (Control M) := by
  letI := M.ΛFin
  letI := M.σFin
  infer_instance

noncomputable instance cellFintype (M : Turing.FinTM2) (height : ℕ) : Fintype (Cell M height) := by
  letI := M.kFin
  infer_instance

/-- The constants depend only on the fixed verifier, not its input. -/
noncomputable def controlBits (M : Turing.FinTM2) : ℕ := Fintype.card (Control M)
noncomputable def symbolBits (M : Turing.FinTM2) : ℕ := by
  letI := M.kFin
  exact ∑ k : M.K, (Fintype.card (Symbol M k)+1)

theorem cell_card (M : Turing.FinTM2) (height : ℕ) :
    Fintype.card (Cell M height) = controlBits M+height*symbolBits M := by
  letI := M.kFin
  simp only [Cell,Fintype.card_sum,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin,
    Fintype.card_option,controlBits,symbolBits,Finset.mul_sum]

/-- Boolean code, including a unique empty marker at every unused stack slot. -/
noncomputable def encode (M : Turing.FinTM2) (height : ℕ) (c : M.Cfg) : Cell M height → Bool := by
  classical
  exact fun cell => match cell with
    | .inl q => decide ((c.l,c.var) = q)
    | .inr ⟨k,(i,a)⟩ => decide ((c.stk k)[i.val]? = a.map Subtype.val)

/-- The valid bounded configurations actually reached by the verifier. -/
def Valid (M : Turing.FinTM2) (height : ℕ) (c : M.Cfg) : Prop :=
  TM2Alphabet.Supported (TM2Alphabet.alphabet M) c.stk ∧
  ∀ k, (c.stk k).length ≤ height

lemma stack_slot_exists (M : Turing.FinTM2) (height : ℕ) (c : M.Cfg)
    (hc : Valid M height c) (k : M.K) (i : Fin height) :
    ∃ a : Option (Symbol M k), (c.stk k)[i.val]? = a.map Subtype.val := by
  cases h : (c.stk k)[i.val]? with
  | none => exact ⟨none,rfl⟩
  | some a =>
    have ha : a ∈ c.stk k := List.mem_of_getElem? h
    exact ⟨some ⟨a,hc.1 k a ha⟩,rfl⟩

/-- Equality of these polynomial-size Boolean codes implies equality of the
entire original configurations, including every stack and control component. -/
theorem encode_injective_on_valid (M : Turing.FinTM2) (height : ℕ) {c d : M.Cfg}
    (hc : Valid M height c) (hd : Valid M height d)
    (he : encode M height c = encode M height d) : c = d := by
  classical
  have hctrl : (c.l,c.var) = (d.l,d.var) := by
    have h := congrFun he (Sum.inl (c.l,c.var))
    have htrue : encode M height c (Sum.inl (c.l,c.var)) = true := by simp [encode]
    rw [htrue] at h
    have hd' : (d.l,d.var) = (c.l,c.var) := by
      apply of_decide_eq_true
      exact h.symm
    exact hd'.symm
  have hstk : c.stk = d.stk := by
    funext k
    apply List.ext_getElem?
    intro i
    by_cases hi : i < height
    · obtain ⟨a,ha⟩ := stack_slot_exists M height c hc k ⟨i,hi⟩
      have h := congrFun he (Sum.inr ⟨k,(⟨i,hi⟩,a)⟩)
      have htrue : encode M height c (Sum.inr ⟨k,(⟨i,hi⟩,a)⟩) = true := by simp [encode,ha]
      rw [htrue] at h
      have hd' : (d.stk k)[i]? = a.map Subtype.val := by
        apply of_decide_eq_true
        exact h.symm
      exact ha.trans hd'.symm
    · rw [List.getElem?_eq_none (by have := hc.2 k;omega),
        List.getElem?_eq_none (by have := hd.2 k;omega)]
  rcases c with ⟨cl,cv,cs⟩
  rcases d with ⟨dl,dv,ds⟩
  obtain ⟨hl,hv⟩ := Prod.mk.inj hctrl
  cases hl
  cases hv
  cases hstk
  rfl

/-- Every actual input tableau lies in the domain of the faithful Boolean code. -/
theorem input_tableau_valid (M : Turing.FinTM2) (x : List (M.Γ M.k₀)) (t : ℕ) :
    Valid M (x.length+t*TM2Space.machineBudget M)
      ((stutter M.step)^[t] (Turing.initList M x)) :=
  ⟨TM2Alphabet.tableau_supported M x t,TM2Space.input_tableau_stack_bound M x t⟩

end HiddenCircuits.Complexity.TM2BooleanEncoding
