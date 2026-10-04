import HiddenCircuits.Complexity.BinaryArithmetic.Multiplication
import HiddenCircuits.Complexity.BinaryArithmetic.DivisionBits
import HiddenCircuits.Complexity.BinaryArithmetic.SubtractionMachine

/-! Long-division control, composed entirely from finite bit-stack blocks. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic
open OracleBlock OracleMachine

def divStore (scratch d r q bits a z t flag : BitString) : Store 8 := fun i =>
  if i.val = 0 then scratch else if i.val = 1 then d else if i.val = 2 then r
  else if i.val = 3 then q else if i.val = 4 then bits else if i.val = 5 then a
  else if i.val = 6 then z else if i.val = 7 then t else flag

noncomputable def divShift (b : Bool) : OracleBlock 8 := if b then push 2 true else doubleOn 2

def divShiftCost (r : BitString) (b : Bool) : ℕ := if b then 1 else doubleCost r

lemma divShiftCost_le (r : BitString) (b : Bool) : divShiftCost r b ≤ 3 := by
  cases b
  · exact doubleCost_le r
  · simp [divShiftCost]

theorem divShift_executes (g : BitString → ℕ) (d r q bits : BitString) (b : Bool) :
    (divShift b).Executes g (divStore [] d r q bits [] [] [] [])
      (divStore [] d (shiftBit r b) q bits [] [] [] []) (divShiftCost r b) := by
  cases b
  · convert doubleOn_executes g (2 : Fin 9) (divStore [] d r q bits [] [] [] []) using 1
    funext i; fin_cases i <;> rfl
  · convert push_executes g (2 : Fin 9) true (divStore [] d r q bits [] [] [] []) using 1
    funext i; fin_cases i <;> rfl

noncomputable def divCopyR : OracleBlock 8 := copyOn 2 5 0 (by decide) (by decide) (by decide)
noncomputable def divCopyD : OracleBlock 8 := copyOn 1 6 0 (by decide) (by decide) (by decide)

theorem divCopyR_executes (g : BitString → ℕ) (d r q bits : BitString) :
    divCopyR.Executes g (divStore [] d r q bits [] [] [] [])
      (divStore [] d r q bits r [] [] []) (5*r.length+2) := by
  convert copyOn_executes g (2 : Fin 9) 5 0 (by decide) (by decide) (by decide)
    (divStore [] d r q bits [] [] [] []) rfl using 1
  funext i; fin_cases i <;> simp [divStore]

theorem divCopyD_executes (g : BitString → ℕ) (d r q bits : BitString) :
    divCopyD.Executes g (divStore [] d r q bits r [] [] [])
      (divStore [] d r q bits r d [] []) (5*d.length+2) := by
  convert copyOn_executes g (1 : Fin 9) 6 0 (by decide) (by decide) (by decide)
    (divStore [] d r q bits r [] [] []) rfl using 1
  funext i; fin_cases i <;> simp [divStore]

/-- Borrow branch: discard the difference and emit a zero quotient bit. -/
noncomputable def divKeep : OracleBlock 8 := seq (clear 5) (doubleOn 3)

theorem divKeep_executes (g : BitString → ℕ) (d r q bits diff : BitString) :
    divKeep.Executes g (divStore [] d r q bits diff [] [] [])
      (divStore [] d r (doubleBits q) bits [] [] [] []) (diff.length+doubleCost q+3) := by
  have hc : (clear (5 : Fin 9)).Executes g (divStore [] d r q bits diff [] [] [])
      (divStore [] d r q bits [] [] [] []) (diff.length+1) := by
    convert clear_executes g (5 : Fin 9) (divStore [] d r q bits diff [] [] []) using 1
    funext i; fin_cases i <;> rfl
  have hd : (doubleOn (3 : Fin 9)).Executes g (divStore [] d r q bits [] [] [] [])
      (divStore [] d r (doubleBits q) bits [] [] [] []) (doubleCost q) := by
    convert doubleOn_executes g (3 : Fin 9) (divStore [] d r q bits [] [] [] []) using 1
    funext i; fin_cases i <;> rfl
  have h := seq_executes _ _ g hc hd
  convert h using 1 <;> omega

/-- Non-borrow branch: install the difference and emit a one quotient bit. -/
noncomputable def divUse : OracleBlock 8 :=
  seq (clear 2) (seq (reverseOn 5 0 (by decide)) (seq (reverseOn 0 2 (by decide)) (push 3 true)))

theorem divUse_executes (g : BitString → ℕ) (d r q bits diff : BitString) :
    divUse.Executes g (divStore [] d r q bits diff [] [] [])
      (divStore [] d diff (true::q) bits [] [] [] []) (r.length+4*diff.length+10) := by
  have hc : (clear (2 : Fin 9)).Executes g (divStore [] d r q bits diff [] [] [])
      (divStore [] d [] q bits diff [] [] []) (r.length+1) := by
    convert clear_executes g (2 : Fin 9) (divStore [] d r q bits diff [] [] []) using 1
    funext i; fin_cases i <;> rfl
  have hr₁ : (reverseOn (5 : Fin 9) 0 (by decide)).Executes g (divStore [] d [] q bits diff [] [] [])
      (divStore diff.reverse d [] q bits [] [] [] []) (2*diff.length+1) := by
    convert reverseOn_executes g (5 : Fin 9) 0 (by decide) (divStore [] d [] q bits diff [] [] []) using 1
    funext i; fin_cases i <;> simp [divStore]
  have hr₂ : (reverseOn (0 : Fin 9) 2 (by decide)).Executes g (divStore diff.reverse d [] q bits [] [] [] [])
      (divStore [] d diff q bits [] [] [] []) (2*diff.length+1) := by
    convert reverseOn_executes g (0 : Fin 9) 2 (by decide) (divStore diff.reverse d [] q bits [] [] [] []) using 1
    · funext i; fin_cases i <;> simp [divStore]
    · simp [divStore]
  have hp : (push (3 : Fin 9) true).Executes g (divStore [] d diff q bits [] [] [] [])
      (divStore [] d diff (true::q) bits [] [] [] []) 1 := by
    convert push_executes g (3 : Fin 9) true (divStore [] d diff q bits [] [] [] []) using 1
    funext i; fin_cases i <;> rfl
  have h := seq_executes _ _ g hc (seq_executes _ _ g hr₁ (seq_executes _ _ g hr₂ hp))
  convert h using 1 <;> omega

noncomputable def divSelect : OracleBlock 8 := branchPop 8 skip divUse divKeep

def divSelectCost (d r q : BitString) : ℕ :=
  if value r < value d then (Computability.encodeNat (value r-value d)).length+doubleCost q+5
  else r.length+4*(Computability.encodeNat (value r-value d)).length+12

theorem divSelectCost_le (d r q : BitString) (hr : Canonical r) :
    divSelectCost d r q ≤ 5*r.length+12 := by
  have hl : (Computability.encodeNat (value r-value d)).length ≤ r.length :=
    canonical_length_mono (canonical_encodeNat _) hr (by simp)
  have hd := doubleCost_le q
  unfold divSelectCost
  split <;> omega

theorem divSelect_executes (g : BitString → ℕ) (d r q bits : BitString) :
    divSelect.Executes g
      (divStore [] d r q bits (Computability.encodeNat (value r-value d)) [] [] [decide (value r<value d)])
      (if value r<value d then divStore [] d r (doubleBits q) bits [] [] [] []
        else divStore [] d (Computability.encodeNat (value r-value d)) (true::q) bits [] [] [] [])
      (divSelectCost d r q) := by
  have hup (b : Bool) : Function.update
      (divStore [] d r q bits (Computability.encodeNat (value r-value d)) [] [] [b]) (8 : Fin 9) [] =
      divStore [] d r q bits (Computability.encodeNat (value r-value d)) [] [] [] := by
    funext i; fin_cases i <;> rfl
  by_cases h : value r<value d
  · simp only [h,decide_true,ite_true,divSelectCost]
    have hb := branchPop_true (8 : Fin 9) skip divUse divKeep g
      (s := divStore [] d r q bits (Computability.encodeNat (value r-value d)) [] [] [true]) rfl
      (by rw [hup]; exact divKeep_executes g d r q bits (Computability.encodeNat (value r-value d)))
    convert hb using 1 <;> omega
  · simp only [h,decide_false,ite_false,divSelectCost]
    have hb := branchPop_false (8 : Fin 9) skip divUse divKeep g
      (s := divStore [] d r q bits (Computability.encodeNat (value r-value d)) [] [] [false]) rfl
      (by rw [hup]; exact divUse_executes g d r q bits (Computability.encodeNat (value r-value d)))
    convert hb using 1 <;> omega

def divSubEmbedding : Fin 4 ↪ Fin 9 where
  toFun i := ⟨i.val+5,by omega⟩
  inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; simp only at this; omega

noncomputable def divSubtract : OracleBlock 8 := rename subBlock divSubEmbedding

theorem divSubtract_executes (g : BitString → ℕ) (d r q bits : BitString) :
    divSubtract.Executes g (divStore [] d r q bits r d [] [])
      (divStore [] d r q bits (Computability.encodeNat (value r-value d)) [] [] [decide (value r<value d)])
      (subCost r d) := by
  have h := subBlock_executes g r d
  rw [subtractBits_correct] at h
  have hb : (subRaw r d false).2 = decide (value r<value d) := by
    apply Bool.eq_iff_iff.mpr
    simpa using subRaw_borrow r d
  rw [hb] at h
  apply rename_executes_to subBlock divSubEmbedding g h
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · intro j hj
    fin_cases j
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact False.elim (hj 0 rfl)
    · exact False.elim (hj 1 rfl)
    · exact False.elim (hj 2 rfl)
    · exact False.elim (hj 3 rfl)

noncomputable def divBody (b : Bool) : OracleBlock 8 :=
  seq (divShift b) (seq divCopyR (seq divCopyD (seq divSubtract divSelect)))

def divBodyCost (d r q : BitString) (b : Bool) : ℕ :=
  divShiftCost r b+(5*(shiftBit r b).length+2)+(5*d.length+2)+
    subCost (shiftBit r b) d+divSelectCost d (shiftBit r b) q+8

theorem divBody_executes (g : BitString → ℕ) (d r q bits : BitString) (b : Bool) :
    (divBody b).Executes g (divStore [] d r q bits [] [] [] [])
      (divStore [] d (divStepBits d r q b).1 (divStepBits d r q b).2 bits [] [] [] [])
      (divBodyCost d r q b) := by
  have hs := divShift_executes g d r q bits b
  have h₁ := divCopyR_executes g d (shiftBit r b) q bits
  have h₂ := divCopyD_executes g d (shiftBit r b) q bits
  have h₃ := divSubtract_executes g d (shiftBit r b) q bits
  have h₄ := divSelect_executes g d (shiftBit r b) q bits
  have he : (if value (shiftBit r b)<value d then divStore [] d (shiftBit r b) (doubleBits q) bits [] [] [] []
      else divStore [] d (Computability.encodeNat (value (shiftBit r b)-value d)) (true::q) bits [] [] [] []) =
      divStore [] d (divStepBits d r q b).1 (divStepBits d r q b).2 bits [] [] [] [] := by
    by_cases hc : value (shiftBit r b)<value d <;> simp only [divStepBits,hc,ite_true,ite_false]
  rw [he] at h₄
  have h := seq_executes _ _ g hs (seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ h₄)))
  convert h using 1 <;> unfold divBodyCost <;> omega

/-- Each division iteration has linear cost in the remainder and divisor bits. -/
theorem divBodyCost_le (d r q : BitString) (b : Bool) (hr : Canonical r) :
    divBodyCost d r q b ≤ 15*r.length+10*d.length+50 := by
  have h₁ := divShiftCost_le r b
  have h₂ := length_shiftBit r b
  have h₃ := subCost_bound (shiftBit r b) d
  have h₄ := divSelectCost_le d (shiftBit r b) q (canonical_shiftBit hr b)
  unfold divBodyCost
  omega

noncomputable def divLoop : OracleBlock 8 := whilePop 4 (divBody false) (divBody true)

def divLoopCost (d : BitString) : BitString → BitString → BitString → ℕ
  | [], _, _ => 1
  | b::bs, r, q => 2+divBodyCost d r q b+
      divLoopCost d bs (divStepBits d r q b).1 (divStepBits d r q b).2

theorem divLoop_executes (g : BitString → ℕ) (d bits r q : BitString) :
    divLoop.Executes g (divStore [] d r q bits [] [] [] [])
      (divStore [] d (divFoldBits d bits r q).1 (divFoldBits d bits r q).2 [] [] [] [] [])
      (divLoopCost d bits r q) := by
  apply whilePop_executes
  induction bits generalizing r q with
  | nil => exact WhileExecution.empty _ rfl
  | cons b bs ih =>
    have hup : Function.update (divStore [] d r q (b::bs) [] [] [] []) (4 : Fin 9) bs =
        divStore [] d r q bs [] [] [] [] := by funext i; fin_cases i <;> rfl
    cases b
    · have h := WhileExecution.zero rfl
        (show (divBody false).Executes g (Function.update (divStore [] d r q (false::bs) [] [] [] []) 4 bs)
          (divStore [] d (divStepBits d r q false).1 (divStepBits d r q false).2 bs [] [] [] [])
          (divBodyCost d r q false) by rw [hup]; exact divBody_executes g d r q bs false)
        (ih (divStepBits d r q false).1 (divStepBits d r q false).2)
      convert h using 1 <;> simp only [divFoldBits,divLoopCost] <;> omega
    · have h := WhileExecution.one rfl
        (show (divBody true).Executes g (Function.update (divStore [] d r q (true::bs) [] [] [] []) 4 bs)
          (divStore [] d (divStepBits d r q true).1 (divStepBits d r q true).2 bs [] [] [] [])
          (divBodyCost d r q true) by rw [hup]; exact divBody_executes g d r q bs true)
        (ih (divStepBits d r q true).1 (divStepBits d r q true).2)
      convert h using 1 <;> simp only [divFoldBits,divLoopCost] <;> omega

/-- The remainder bound makes every iteration uniformly linear in divisor size. -/
theorem divLoopCost_le (d bits r q : BitString) (hd : Canonical d) (hr : Canonical r) (hq : Canonical q)
    (hlt : value r<value d) :
    divLoopCost d bits r q ≤ 1+bits.length*(25*d.length+52) := by
  induction bits generalizing r q with
  | nil => simp [divLoopCost]
  | cons b bs ih =>
    have hs := divBodyCost_le d r q b hr
    have hl := canonical_length_mono hr hd hlt.le
    obtain ⟨hr',hq'⟩ := divStepBits_canonical (d := d) hr hq b
    have hv := congrArg Prod.fst (divStepBits_value d r q b)
    change value (divStepBits d r q b).1 = (divStepNat (value d) (value r) (value q) b).1 at hv
    have hh : value (divStepBits d r q b).1<value d := by
      rw [hv]
      exact divStepNat_remainder _ _ _ _ hlt
    have hi := ih _ _ hr' hq' hh
    simp only [divLoopCost,List.length_cons]
    nlinarith

noncomputable def divisionBlock : OracleBlock 8 := seq (reverseOn 0 4 (by decide)) divLoop

theorem divisionBlock_executes (g : BitString → ℕ) (x d : BitString) :
    divisionBlock.Executes g (divStore x d [] [] [] [] [] [] [])
      (divStore [] d (divFoldBits d x.reverse [] []).1 (divFoldBits d x.reverse [] []).2 [] [] [] [] [])
      (2*x.length+divLoopCost d x.reverse [] []+3) := by
  have hr : (reverseOn (0 : Fin 9) 4 (by decide)).Executes g (divStore x d [] [] [] [] [] [] [])
      (divStore [] d [] [] x.reverse [] [] [] []) (2*x.length+1) := by
    convert reverseOn_executes g (0 : Fin 9) 4 (by decide) (divStore x d [] [] [] [] [] [] []) using 1
    funext i; fin_cases i <;> simp [divStore]
  have h := seq_executes _ _ g hr (divLoop_executes g d x.reverse [] [])
  convert h using 1 <;> omega

/-- A fixed finite bit program for Euclidean division with a quadratic bound. -/
theorem divide_binary_output (g : BitString → ℕ) (m n : ℕ) (hn : 0<n) :
    ∃ t : ℕ, divisionBlock.Executes g
      (divStore (Computability.encodeNat m) (Computability.encodeNat n) [] [] [] [] [] [] [])
      (divStore [] (Computability.encodeNat n) (Computability.encodeNat (m%n))
        (Computability.encodeNat (m/n)) [] [] [] [] []) t ∧
      t ≤ (Computability.encodeNat m).length*(25*(Computability.encodeNat n).length+54)+4 := by
  refine ⟨2*(Computability.encodeNat m).length+
    divLoopCost (Computability.encodeNat n) (Computability.encodeNat m).reverse [] []+3,?_,?_⟩
  · simpa [divFoldBits_encodeNat m n hn] using
      divisionBlock_executes g (Computability.encodeNat m) (Computability.encodeNat n)
  · have h := divLoopCost_le (Computability.encodeNat n) (Computability.encodeNat m).reverse [] []
      (canonical_encodeNat n) canonical_nil canonical_nil (by simpa using hn)
    simp only [List.length_reverse] at h
    nlinarith

/-- Exact divisibility clears the remainder as well as every work stack. -/
theorem exact_divide_binary_output (g : BitString → ℕ) (m n : ℕ) (hn : 0<n) (hdiv : n ∣ m) :
    ∃ t : ℕ, divisionBlock.Executes g
      (divStore (Computability.encodeNat m) (Computability.encodeNat n) [] [] [] [] [] [] [])
      (divStore [] (Computability.encodeNat n) [] (Computability.encodeNat (m/n)) [] [] [] [] []) t ∧
      t ≤ (Computability.encodeNat m).length*(25*(Computability.encodeNat n).length+54)+4 := by
  simpa [Nat.mod_eq_zero_of_dvd hdiv,Computability.encodeNat,Computability.encodeNum] using
    divide_binary_output g m n hn

lemma divBody_queryFree (b : Bool) : (divBody b).QueryFree := by
  have hs : (divShift b).QueryFree := by
    cases b
    · exact doubleOn_queryFree _
    · exact push_queryFree _ _
  have hk : divKeep.QueryFree := seq_queryFree _ _ (clear_queryFree _) (doubleOn_queryFree _)
  have hu : divUse.QueryFree := seq_queryFree _ _ (clear_queryFree _)
    (seq_queryFree _ _ (reverseOn_queryFree _ _ _) (seq_queryFree _ _ (reverseOn_queryFree _ _ _) (push_queryFree _ _)))
  have hsel : divSelect.QueryFree := branchPop_queryFree _ _ _ _ skip_queryFree hu hk
  exact seq_queryFree _ _ hs (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
      (seq_queryFree _ _ (rename_queryFree _ _ subBlock_queryFree) hsel)))

lemma divisionBlock_queryFree : divisionBlock.QueryFree :=
  seq_queryFree _ _ (reverseOn_queryFree _ _ _) (whilePop_queryFree _ _ _ (divBody_queryFree false) (divBody_queryFree true))

end HiddenCircuits.Complexity.BinaryArithmetic
