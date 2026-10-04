import HiddenCircuits.Complexity.BinaryArithmetic.RationalNormalizeTyped

/-! A literal zero-denominator branch makes the signed-ratio normalizer total. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic.RationalNormalize
open OracleBlock Polynomial

noncomputable def literalOn {k : ℕ} (i : Fin (k+1)) : BitString → OracleBlock k
  | [] => skip
  | b::bs => seq (literalOn i bs) (push i b)
lemma literalOn_executes {k : ℕ} (g : BitString → ℕ) (i : Fin (k+1)) (bs : BitString) (s : Store k) :
    (literalOn i bs).Executes g s (Function.update s i (bs++s i)) (3*bs.length+1) := by
  induction bs with
  | nil => simpa using skip_executes g s
  | cons b bs ih =>
    have hp:=push_executes g i b (Function.update s i (bs++s i))
    simp only [Function.update_self,Function.update_idem] at hp
    convert seq_executes _ _ g ih hp using 1 <;> simp only [List.length_cons] <;> omega
lemma literalOn_queryFree {k : ℕ} (i : Fin (k+1)) (bs : BitString) : (literalOn i bs).QueryFree := by
  induction bs with
  | nil => exact skip_queryFree
  | cons b bs ih => exact seq_queryFree _ _ ih (push_queryFree _ _)

noncomputable def zeroBranch : OracleBlock 15 :=
  seq (clear 9) (literalOn 0 (RationalOracleEncoding.bits 0))
lemma zero_bits_length : (RationalOracleEncoding.bits 0).length=5 := rfl
lemma zeroBranch_executes (g : BitString → ℕ) (u : ℤ) :
    zeroBranch.Executes g (regState (signedBits u) [] [])
      (Function.update (fun _=>[]) 0 (RationalOracleEncoding.bits 0)) ((signedBits u).length+19) := by
  have hc : (clear (9:Fin 16)).Executes g (regState (signedBits u) [] []) (fun _=>[])
      ((signedBits u).length+1) := by
    convert clear_executes g (9:Fin 16) (regState (signedBits u) [] []) using 1
    funext i;fin_cases i <;> rfl
  have hl:=literalOn_executes g (0:Fin 16) (RationalOracleEncoding.bits 0) (fun _=>[])
  simp only [List.append_nil,zero_bits_length] at hl
  convert seq_executes _ _ g hc hl using 1 <;> omega

noncomputable def restoreDen (s b : Bool) : OracleBlock 15 := seq (push 10 b) (push 10 s)
noncomputable def dispatchBody (s : Bool) : OracleBlock 15 :=
  branchPop 10 zeroBranch (seq (restoreDen s false) program) (seq (restoreDen s true) program)
noncomputable def dispatch : OracleBlock 15 := branchPop 10 zeroBranch (dispatchBody false) (dispatchBody true)
noncomputable def dispatchTime : Polynomial ℕ := time+X+30

lemma restoreDen_executes (g : BitString → ℕ) (u v : ℤ) (b : Bool) (bs : BitString)
    (hb : Computability.encodeNat v.natAbs=b::bs) :
    (restoreDen (negative v) b).Executes g (regState (signedBits u) bs [])
      (regState (signedBits u) (signedBits v) []) 4 := by
  have h1 : (push (10:Fin 16) b).Executes g (regState (signedBits u) bs [])
      (regState (signedBits u) (b::bs) []) 1 := by
    convert push_executes g (10:Fin 16) b _ using 1
    funext i;fin_cases i <;> rfl
  have h2 : (push (10:Fin 16) (negative v)).Executes g (regState (signedBits u) (b::bs) [])
      (regState (signedBits u) (signedBits v) []) 1 := by
    convert push_executes g (10:Fin 16) (negative v) _ using 1
    funext i;fin_cases i <;> simp only [signedBits,hb] <;> rfl
  exact seq_executes _ _ g h1 h2

lemma dispatch_nonzero_executes (g : BitString → ℕ) (u v : ℤ) (hv : v≠0) :
    ∃c,dispatch.Executes g (regState (signedBits u) (signedBits v) [])
      (Function.update (fun _=>[]) 0 (RationalOracleEncoding.bits ((u:ℚ)/(v:ℚ)))) c ∧
      c≤time.eval ((signedBits u).length+(signedBits v).length)+10 := by
  obtain ⟨c,hc,hcb⟩:=program_executes g u v hv
  have hn : Computability.encodeNat v.natAbs≠[] := by
    intro h;exact hv (Int.natAbs_eq_zero.mp ((encodeNat_eq_nil_iff _).mp h))
  cases he : Computability.encodeNat v.natAbs with
  | nil => exact False.elim (hn he)
  | cons b bs =>
    have hp:=seq_executes _ _ g (restoreDen_executes g u v b bs he) hc
    have hup (xs ys : BitString) : Function.update (regState (signedBits u) xs []) (10:Fin 16) ys=
        regState (signedBits u) ys [] := by funext i;fin_cases i <;> rfl
    have hbody : (dispatchBody (negative v)).Executes g
        (regState (signedBits u) (Computability.encodeNat v.natAbs) [])
        (Function.update (fun _=>[]) 0 (RationalOracleEncoding.bits ((u:ℚ)/(v:ℚ)))) (c+8) := by
      cases b
      · convert branchPop_false (10:Fin 16) _ _ _ g
          (show regState (signedBits u) (Computability.encodeNat v.natAbs) [] 10=false::bs from he)
          (by rw [hup];exact hp) using 1 <;> omega
      · convert branchPop_true (10:Fin 16) _ _ _ g
          (show regState (signedBits u) (Computability.encodeNat v.natAbs) [] 10=true::bs from he)
          (by rw [hup];exact hp) using 1 <;> omega
    refine ⟨c+10,?_,by omega⟩
    cases hs : negative v
    · convert branchPop_false (10:Fin 16) _ _ _ g
        (show regState (signedBits u) (signedBits v) [] 10=false::Computability.encodeNat v.natAbs by simp only [signedBits,hs];rfl)
        (by rw [hup];simpa [hs] using hbody) using 1 <;> omega
    · convert branchPop_true (10:Fin 16) _ _ _ g
        (show regState (signedBits u) (signedBits v) [] 10=true::Computability.encodeNat v.natAbs by simp only [signedBits,hs];rfl)
        (by rw [hup];simpa [hs] using hbody) using 1 <;> omega

/-- Canonical signed inputs include zero denominators; those map literally to zero. -/
theorem dispatch_executes (g : BitString → ℕ) (u v : ℤ) :
    ∃c,dispatch.Executes g (regState (signedBits u) (signedBits v) [])
      (Function.update (fun _=>[]) 0 (RationalOracleEncoding.bits ((u:ℚ)/(v:ℚ)))) c ∧
      c≤dispatchTime.eval ((signedBits u).length+(signedBits v).length) := by
  by_cases hv:v=0
  · subst v
    have h0:=zeroBranch_executes g u
    have he : (dispatchBody false).Executes g (regState (signedBits u) [] [])
        (Function.update (fun _=>[]) 0 (RationalOracleEncoding.bits 0)) ((signedBits u).length+21) := by
      convert branchPop_empty (10:Fin 16) _ _ _ g rfl h0 using 1 <;> omega
    have hup : Function.update (regState (signedBits u) (signedBits 0) []) (10:Fin 16) []=
        regState (signedBits u) [] [] := by funext i;fin_cases i <;> rfl
    refine ⟨(signedBits u).length+23,?_,?_⟩
    · have hh:=branchPop_false (10:Fin 16) zeroBranch (dispatchBody false) (dispatchBody true) g
        (s:=regState (signedBits u) (signedBits 0) []) (rest:=[]) rfl (by rw [hup];exact he)
      simpa using hh
    · simp only [dispatchTime,eval_add,eval_X,eval_ofNat]
      omega
  · obtain ⟨c,hc,hcb⟩:=dispatch_nonzero_executes g u v hv
    exact ⟨c,hc,by simp only [dispatchTime,eval_add,eval_X,eval_ofNat];omega⟩

lemma zeroBranch_queryFree : zeroBranch.QueryFree := seq_queryFree _ _ (clear_queryFree _) (literalOn_queryFree _ _)
lemma restoreDen_queryFree (s b : Bool) : (restoreDen s b).QueryFree :=
  seq_queryFree _ _ (push_queryFree _ _) (push_queryFree _ _)
lemma dispatchBody_queryFree (s : Bool) : (dispatchBody s).QueryFree :=
  branchPop_queryFree _ _ _ _ zeroBranch_queryFree
    (seq_queryFree _ _ (restoreDen_queryFree _ _) program_queryFree)
    (seq_queryFree _ _ (restoreDen_queryFree _ _) program_queryFree)
lemma dispatch_queryFree : dispatch.QueryFree :=
  branchPop_queryFree _ _ _ _ zeroBranch_queryFree (dispatchBody_queryFree false) (dispatchBody_queryFree true)

end HiddenCircuits.Complexity.BinaryArithmetic.RationalNormalize
