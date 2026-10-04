import HiddenCircuits.Complexity.BinaryArithmetic.SignedBits
import HiddenCircuits.Complexity.BinaryArithmetic.SubtractionMachine
import HiddenCircuits.Complexity.BinaryArithmetic.DivisionBits
import HiddenCircuits.Complexity.OracleCleanup

/-! Signed addition dispatches to real unsigned addition or borrow/subtraction blocks. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic
open OracleBlock OracleMachine

def signedAddStore (x y t bx by_ f g : BitString) : Store 6 := fun i =>
  if i.val=0 then x else if i.val=1 then y else if i.val=2 then t else
    if i.val=3 then bx else if i.val=4 then by_ else if i.val=5 then f else g

def signedAddEmbedding : Fin 3 ↪ Fin 7 where
  toFun i := i.castLE (by decide)
  inj' := by intro i j h; exact Fin.ext (congrArg (fun q : Fin 7 => q.val) h)

def signedSubEmbedding : Fin 4 ↪ Fin 7 where
  toFun i := if i.val=3 then 5 else ⟨i.val,by omega⟩
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

def signedReverseSubEmbedding : Fin 4 ↪ Fin 7 where
  toFun i := if i.val=0 then 4 else if i.val=1 then 3 else if i.val=2 then 2 else 6
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

noncomputable def signedAddMagnitude : OracleBlock 6 := rename addBlock signedAddEmbedding
noncomputable def signedSubtractMagnitude : OracleBlock 6 := rename subBlock signedSubEmbedding
noncomputable def signedReverseSubtract : OracleBlock 6 := rename subBlock signedReverseSubEmbedding

 theorem signedAddMagnitude_executes (g : BitString → ℕ) (x y : BitString) :
    signedAddMagnitude.Executes g (signedAddStore x y [] [] [] [] [])
      (signedAddStore (addBits x y false) [] [] [] [] [] []) (addCost x y) := by
  apply rename_executes_to addBlock signedAddEmbedding g (addBlock_executes g x y)
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · intro i hi; fin_cases i <;> first | rfl | (exfalso; exact hi 0 rfl) | (exfalso; exact hi 1 rfl) | (exfalso; exact hi 2 rfl)

 theorem signedSubtractMagnitude_executes (g : BitString → ℕ) (x y : BitString) :
    signedSubtractMagnitude.Executes g (signedAddStore x y [] x y [] [])
      (signedAddStore (subtractBits x y) [] [] x y [(subRaw x y false).2] []) (subCost x y) := by
  apply rename_executes_to subBlock signedSubEmbedding g (subBlock_executes g x y)
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · intro i hi; fin_cases i <;> first | rfl | (exfalso; exact hi 0 rfl) | (exfalso; exact hi 1 rfl) | (exfalso; exact hi 2 rfl) | (exfalso; exact hi 3 rfl)

 theorem signedReverseSubtract_executes (g : BitString → ℕ) (x y : BitString) :
    signedReverseSubtract.Executes g (signedAddStore [] [] [] x y [] [])
      (signedAddStore [] [] [] [] (subtractBits y x) [] [(subRaw y x false).2]) (subCost y x) := by
  apply rename_executes_to subBlock signedReverseSubEmbedding g (subBlock_executes g y x)
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · intro i hi; fin_cases i <;> first | rfl | (exfalso; exact hi 0 rfl) | (exfalso; exact hi 1 rfl) | (exfalso; exact hi 2 rfl) | (exfalso; exact hi 3 rfl)

noncomputable def signedCopyLeft : OracleBlock 6 := copyOn 0 3 2 (by decide) (by decide) (by decide)
noncomputable def signedCopyRight : OracleBlock 6 := copyOn 1 4 2 (by decide) (by decide) (by decide)
noncomputable def signedCopyResult : OracleBlock 6 := copyOn 4 0 2 (by decide) (by decide) (by decide)

 theorem signedCopyLeft_executes (g : BitString → ℕ) (x y : BitString) :
    signedCopyLeft.Executes g (signedAddStore x y [] [] [] [] [])
      (signedAddStore x y [] x [] [] []) (5*x.length+2) := by
  convert copyOn_executes g (0:Fin 7) 3 2 (by decide) (by decide) (by decide)
    (signedAddStore x y [] [] [] [] []) rfl using 1
  funext i; fin_cases i <;> simp [signedAddStore]

 theorem signedCopyRight_executes (g : BitString → ℕ) (x y : BitString) :
    signedCopyRight.Executes g (signedAddStore x y [] x [] [] [])
      (signedAddStore x y [] x y [] []) (5*y.length+2) := by
  convert copyOn_executes g (1:Fin 7) 4 2 (by decide) (by decide) (by decide)
    (signedAddStore x y [] x [] [] []) rfl using 1
  funext i; fin_cases i <;> simp [signedAddStore]

 theorem signedCopyResult_executes (g : BitString → ℕ) (z f : BitString) :
    signedCopyResult.Executes g (signedAddStore [] [] [] [] z [] f)
      (signedAddStore z [] [] [] z [] f) (5*z.length+2) := by
  convert copyOn_executes g (4:Fin 7) 0 2 (by decide) (by decide) (by decide)
    (signedAddStore [] [] [] [] z [] f) rfl using 1
  funext i; fin_cases i <;> simp [signedAddStore]

 theorem signedNat_add_same (a : Bool) (m n : ℕ) :
    signedNat a (m+n)=signedNat a m+signedNat a n := by cases a <;> simp [signedNat] <;> ring

 theorem signedNat_sub_left (a b : Bool) (hab : a≠b) (m n : ℕ) (h : n≤m) :
    signedNat a (m-n)=signedNat a m+signedNat b n := by
  cases a <;> cases b <;> simp_all [signedNat,Int.ofNat_sub h] <;> omega

 theorem signedNat_sub_right (a b : Bool) (hab : a≠b) (m n : ℕ) (h : m≤n) :
    signedNat b (n-m)=signedNat a m+signedNat b n := by
  cases a <;> cases b <;> simp_all [signedNat,Int.ofNat_sub h] <;> omega


noncomputable def signedSame (a : Bool) : OracleBlock 6 := seq signedAddMagnitude (finishOn 0 a)
noncomputable def signedReverseBranch (b : Bool) : OracleBlock 6 :=
  seq signedReverseSubtract (seq signedCopyResult (finishOn 0 b))
noncomputable def signedBranch (a b : Bool) : OracleBlock 6 :=
  branchPop 5 skip (finishOn 0 a) (signedReverseBranch b)
noncomputable def signedDifferent (a b : Bool) : OracleBlock 6 :=
  seq signedCopyLeft (seq signedCopyRight (seq signedSubtractMagnitude (signedBranch a b)))
noncomputable def signedMagnitudeSum (a b : Bool) : OracleBlock 6 :=
  if a=b then signedSame a else signedDifferent a b

 theorem signedSame_correct (g : BitString → ℕ) (a : Bool) (m n : ℕ) :
    ∃ t : Store 6, ∃ c : ℕ,
      (signedSame a).Executes g (signedAddStore (Computability.encodeNat m) (Computability.encodeNat n) [] [] [] [] []) t c ∧
      t 0=signedBits (signedNat a m+signedNat a n) ∧
      c≤5*max (Computability.encodeNat m).length (Computability.encodeNat n).length+11 := by
  let x := Computability.encodeNat m
  let y := Computability.encodeNat n
  let u := signedAddStore (addBits x y false) [] [] [] [] [] []
  have hh := seq_executes signedAddMagnitude (finishOn (0:Fin 7) a) g
    (signedAddMagnitude_executes g x y) (finishOn_executes g (0:Fin 7) a u)
  refine ⟨Function.update u 0 (finishSigned a (u 0)),_,hh,?_,?_⟩
  · simp only [Function.update_self]
    change finishSigned a (addBits x y false)=_
    dsimp [x,y]
    rw [addBits_encodeNat]
    simp only [bitVal,Bool.false_eq_true,ite_false,Nat.add_zero]
    rw [finishSigned_encode,signedNat_add_same]
  · have ha := addCost_le x y
    have hf := finishCost_le (u 0)
    dsimp only [x,y] at *
    omega

 theorem signedReverseBranch_correct (g : BitString → ℕ) (b : Bool) (m n : ℕ) :
    ∃ t : Store 6, ∃ c : ℕ,
      (signedReverseBranch b).Executes g (signedAddStore [] [] [] (Computability.encodeNat m) (Computability.encodeNat n) [] []) t c ∧
      t 0=signedBits (signedNat b (n-m)) ∧
      c≤10*max (Computability.encodeNat m).length (Computability.encodeNat n).length+13 := by
  let x := Computability.encodeNat m
  let y := Computability.encodeNat n
  let z := subtractBits y x
  let f := [(subRaw y x false).2]
  let u := signedAddStore z [] [] [] z [] f
  have hh := seq_executes signedReverseSubtract (seq signedCopyResult (finishOn (0:Fin 7) b)) g
    (signedReverseSubtract_executes g x y)
    (seq_executes signedCopyResult (finishOn (0:Fin 7) b) g
      (signedCopyResult_executes g z f) (finishOn_executes g (0:Fin 7) b u))
  refine ⟨Function.update u 0 (finishSigned b (u 0)),_,hh,?_,?_⟩
  · simp only [Function.update_self]
    change finishSigned b z=_
    dsimp [z,x,y]
    rw [subtract_encodeNat,finishSigned_encode]
  · have hs := subCost_bound y x
    have hf := finishCost_le (u 0)
    have hz : z.length≤max x.length y.length := by
      dsimp [z,x,y]
      rw [subtract_encodeNat]
      exact (canonical_length_mono (canonical_encodeNat _) (canonical_encodeNat _)
        (by simpa using Nat.sub_le n m)).trans (Nat.le_max_right _ _)
    rw [max_comm] at hs
    dsimp only [x,y] at *
    omega

 theorem signedBranch_correct (g : BitString → ℕ) (a b : Bool) (hab : a≠b) (m n : ℕ) :
    ∃ t : Store 6, ∃ c : ℕ,
      (signedBranch a b).Executes g
        (signedAddStore (subtractBits (Computability.encodeNat m) (Computability.encodeNat n)) [] []
          (Computability.encodeNat m) (Computability.encodeNat n)
          [(subRaw (Computability.encodeNat m) (Computability.encodeNat n) false).2] []) t c ∧
      t 0=signedBits (signedNat a m+signedNat b n) ∧
      c≤10*max (Computability.encodeNat m).length (Computability.encodeNat n).length+15 := by
  let x := Computability.encodeNat m
  let y := Computability.encodeNat n
  have hb : (subRaw x y false).2=decide (m<n) := by
    apply Bool.eq_iff_iff.mpr
    simpa [x,y] using subRaw_borrow x y
  by_cases hmn : m<n
  · have hs : subtractBits x y=[] := by
      dsimp only [x,y]
      rw [subtract_encodeNat,Nat.sub_eq_zero_of_le hmn.le]
      rfl
    obtain ⟨t,c,hc,ho,hbound⟩ := signedReverseBranch_correct g b m n
    have hh := branchPop_true (5:Fin 7) skip (finishOn (0:Fin 7) a) (signedReverseBranch b) g
      (s := signedAddStore [] [] [] x y [true] []) (by rfl)
      (by convert hc using 1; funext i; fin_cases i <;> simp [signedAddStore,x,y])
    refine ⟨t,c+2,?_,?_,by omega⟩
    · change (signedBranch a b).Executes g (signedAddStore (subtractBits x y) [] [] x y [(subRaw x y false).2] []) _ _
      rw [hb,show decide (m<n)=true by simp [hmn],hs]
      exact hh
    · rw [ho,signedNat_sub_right a b hab m n hmn.le]
  · have hnm : n≤m := by omega
    let u := signedAddStore (subtractBits x y) [] [] x y [] []
    have hf := finishOn_executes g (0:Fin 7) a u
    have hh := branchPop_false (5:Fin 7) skip (finishOn (0:Fin 7) a) (signedReverseBranch b) g
      (s := signedAddStore (subtractBits x y) [] [] x y [false] []) (by rfl)
      (by convert hf using 1; funext i; fin_cases i <;> simp [u,signedAddStore])
    refine ⟨Function.update u 0 (finishSigned a (u 0)),finishCost (u 0)+2,?_,?_,?_⟩
    · change (signedBranch a b).Executes g (signedAddStore (subtractBits x y) [] [] x y [(subRaw x y false).2] []) _ _
      rw [hb,show decide (m<n)=false by simp [hmn]]
      exact hh
    · simp only [Function.update_self]
      change finishSigned a (subtractBits x y)=_
      dsimp [x,y]
      rw [subtract_encodeNat,finishSigned_encode,signedNat_sub_left a b hab m n hnm]
    · have := finishCost_le (u 0); omega


 theorem signedMagnitudeSum_correct (g : BitString → ℕ) (a b : Bool) (m n : ℕ) :
    ∃ t : Store 6, ∃ c : ℕ,
      (signedMagnitudeSum a b).Executes g (signedAddStore (Computability.encodeNat m) (Computability.encodeNat n) [] [] [] [] []) t c ∧
      t 0=signedBits (signedNat a m+signedNat b n) ∧
      c≤40*(max (Computability.encodeNat m).length (Computability.encodeNat n).length+1) := by
  by_cases hab : a=b
  · subst b
    obtain ⟨t,c,hc,ho,hb⟩ := signedSame_correct g a m n
    exact ⟨t,c,by simpa [signedMagnitudeSum] using hc,ho,by omega⟩
  · let x := Computability.encodeNat m
    let y := Computability.encodeNat n
    obtain ⟨t,c,hc,ho,hb⟩ := signedBranch_correct g a b hab m n
    have hh := seq_executes signedCopyLeft
      (seq signedCopyRight (seq signedSubtractMagnitude (signedBranch a b))) g
      (signedCopyLeft_executes g x y)
      (seq_executes signedCopyRight (seq signedSubtractMagnitude (signedBranch a b)) g
        (signedCopyRight_executes g x y)
        (seq_executes signedSubtractMagnitude (signedBranch a b) g
          (signedSubtractMagnitude_executes g x y) hc))
    refine ⟨t,5*x.length+2+(5*y.length+2+(subCost x y+c+2)+2)+2,?_,ho,?_⟩
    · simpa only [signedMagnitudeSum,if_neg hab,signedDifferent] using hh
    · have hs := subCost_bound x y
      have hx := Nat.le_max_left x.length y.length
      have hy := Nat.le_max_right x.length y.length
      dsimp only [x,y] at *
      omega

noncomputable def signedSumRight (a : Bool) : OracleBlock 6 :=
  branchPop 1 skip (signedMagnitudeSum a false) (signedMagnitudeSum a true)
noncomputable def signedSumBlock : OracleBlock 6 :=
  branchPop 0 skip (signedSumRight false) (signedSumRight true)

 theorem signedSum_headers (g : BitString → ℕ) (a b : Bool) {s t : Store 6} {cost : ℕ}
    (h : (signedMagnitudeSum a b).Executes g s t cost) :
    signedSumBlock.Executes g (withSigns s a b) t (cost+4) := by
  have h1 : Function.update (Function.update s (1:Fin 7) (b::s 1)) 1 (s 1)=s := by simp
  have hr : (signedSumRight a).Executes g (Function.update s 1 (b::s 1)) t (cost+2) := by
    cases b
    · exact branchPop_false (1:Fin 7) skip (signedMagnitudeSum a false) (signedMagnitudeSum a true) g (rest := s 1) (by simp) (by rw [h1];exact h)
    · exact branchPop_true (1:Fin 7) skip (signedMagnitudeSum a false) (signedMagnitudeSum a true) g (rest := s 1) (by simp) (by rw [h1];exact h)
  have h0 : Function.update (withSigns s a b) (0:Fin 7) (s 0)=Function.update s 1 (b::s 1) := by
    funext i
    by_cases hi:i=0
    · subst i;simp [withSigns]
    · by_cases hj:i=1
      · subst i;simp [withSigns]
      · simp [withSigns,Function.update_of_ne hi,Function.update_of_ne hj]
  have hs : withSigns s a b (0:Fin 7)=a::s 0 := by simp [withSigns]
  cases a
  · have hh := branchPop_false (0:Fin 7) skip (signedSumRight false) (signedSumRight true) g hs (by rw [h0];exact hr)
    simpa [Nat.add_assoc] using hh
  · have hh := branchPop_true (0:Fin 7) skip (signedSumRight false) (signedSumRight true) g hs (by rw [h0];exact hr)
    simpa [Nat.add_assoc] using hh

/-- A fixed seven-stack, linear-time signed integer adder with canonical zero. -/
theorem signed_add_binary_output (g : BitString → ℕ) (x y : ℤ) :
    ∃ t : Store 6, ∃ c : ℕ,
      signedSumBlock.Executes g (signedAddStore (signedBits x) (signedBits y) [] [] [] [] []) t c ∧
      t 0=signedBits (x+y) ∧
      c≤44*(max (Computability.encodeNat x.natAbs).length (Computability.encodeNat y.natAbs).length+1) := by
  obtain ⟨t,c,hc,ho,hb⟩ := signedMagnitudeSum_correct g (negative x) (negative y) x.natAbs y.natAbs
  have hh := signedSum_headers g (negative x) (negative y) hc
  refine ⟨t,c+4,?_,?_,by omega⟩
  · convert hh using 1
    funext i;fin_cases i <;> simp [withSigns,signedAddStore,signedBits]
  · simpa using ho

 theorem signedSumBlock_queryFree : signedSumBlock.QueryFree := by
  have ha : signedAddMagnitude.QueryFree := rename_queryFree _ _ addBlock_queryFree
  have hs : signedSubtractMagnitude.QueryFree := rename_queryFree _ _ subBlock_queryFree
  have hr : signedReverseSubtract.QueryFree := rename_queryFree _ _ subBlock_queryFree
  have hcL : signedCopyLeft.QueryFree := copyOn_queryFree _ _ _ _ _ _
  have hcR : signedCopyRight.QueryFree := copyOn_queryFree _ _ _ _ _ _
  have hcO : signedCopyResult.QueryFree := copyOn_queryFree _ _ _ _ _ _
  have hsame (a : Bool) : (signedSame a).QueryFree := seq_queryFree _ _ ha (finishOn_queryFree _ _)
  have hrev (b : Bool) : (signedReverseBranch b).QueryFree :=
    seq_queryFree _ _ hr (seq_queryFree _ _ hcO (finishOn_queryFree _ _))
  have hbranch (a b : Bool) : (signedBranch a b).QueryFree :=
    branchPop_queryFree _ _ _ _ skip_queryFree (finishOn_queryFree _ _) (hrev b)
  have hdiff (a b : Bool) : (signedDifferent a b).QueryFree :=
    seq_queryFree _ _ hcL (seq_queryFree _ _ hcR (seq_queryFree _ _ hs (hbranch a b)))
  have hmag (a b : Bool) : (signedMagnitudeSum a b).QueryFree := by
    unfold signedMagnitudeSum
    split_ifs
    · exact hsame a
    · exact hdiff a b
  have hright (a : Bool) : (signedSumRight a).QueryFree :=
    branchPop_queryFree _ _ _ _ skip_queryFree (hmag a false) (hmag a true)
  exact branchPop_queryFree _ _ _ _ skip_queryFree (hright false) (hright true)


noncomputable def signedAddClean : OracleBlock 6 := seq signedSumBlock (cleanup 0)

theorem signedAddClean_queryFree : signedAddClean.QueryFree :=
  seq_queryFree _ _ signedSumBlock_queryFree (cleanup_queryFree _)

/-- A clean seven-stack interface for repeated signed accumulations. -/
theorem signedAddClean_executes (g : BitString → ℕ) (x y : ℤ) :
    ∃ c : ℕ, signedAddClean.Executes g (signedAddStore (signedBits x) (signedBits y) [] [] [] [] [])
      (signedAddStore (signedBits (x+y)) [] [] [] [] [] []) c ∧
      c≤400*(max (Computability.encodeNat x.natAbs).length (Computability.encodeNat y.natAbs).length+1) := by
  obtain ⟨s,c,hc,ho,hb⟩ := signed_add_binary_output g x y
  let L := max (Computability.encodeNat x.natAbs).length (Computability.encodeNat y.natAbs).length
  have hinit : ∀ i : Fin 7, (signedAddStore (signedBits x) (signedBits y) [] [] [] [] [] i).length≤L+1 := by
    intro i
    fin_cases i <;> simp only [signedAddStore,signedBits,List.length_cons,List.length_nil,ite_true,ite_false]
    all_goals dsimp [L]; omega
  have hs := hc.stack_bound hinit
  obtain ⟨d,hd,hbd⟩ := cleanup_executes g (0:Fin 7) s (L+1+c) hs
  refine ⟨c+d+2,?_,?_⟩
  · have hh := seq_executes signedSumBlock (cleanup (0:Fin 7)) g hc hd
    convert hh using 1
    funext i
    fin_cases i <;> simp [signedAddStore,ho]
  · dsimp [L] at hbd
    omega

end HiddenCircuits.Complexity.BinaryArithmetic
