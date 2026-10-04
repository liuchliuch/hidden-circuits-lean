import HiddenCircuits.Complexity.BinaryArithmetic.SignedGcd

/-! Physical canonical sign normalization, preserving the surrounding frame. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic.RationalNormalize
open OracleBlock

noncomputable def negateOn {k : ℕ} (i : Fin (k+1)) : OracleBlock k :=
  branchPop i (push i false) (finishOn i true) (finishOn i false)

lemma signedNat_flip (a : ℤ) : signedNat (!negative a) a.natAbs = -a := by
  conv_rhs => rw [←signedNat_self a]
  cases negative a <;> simp [signedNat]

lemma negateOn_executes {k : ℕ} (g : BitString → ℕ) (i : Fin (k+1))
    (s : Store k) (a : ℤ) (hs : s i=signedBits a) :
    ∃c,(negateOn i).Executes g s (Function.update s i (signedBits (-a))) c ∧ c≤5 := by
  have hf := finishOn_executes g i (!negative a) (Function.update s i (Computability.encodeNat a.natAbs))
  simp only [Function.update_self,Function.update_idem,finishSigned_encode,signedNat_flip] at hf
  refine ⟨finishCost (Computability.encodeNat a.natAbs)+2,?_,by have:=finishCost_le (Computability.encodeNat a.natAbs);omega⟩
  cases hn : negative a
  · exact branchPop_false _ _ _ _ g (by simpa only [signedBits,hn] using hs) (by simpa [hn] using hf)
  · exact branchPop_true _ _ _ _ g (by simpa only [signedBits,hn] using hs) (by simpa [hn] using hf)

lemma negateOn_queryFree {k : ℕ} (i : Fin (k+1)) : (negateOn i).QueryFree :=
  branchPop_queryFree _ _ _ _ (push_queryFree _ _) (finishOn_queryFree _ _) (finishOn_queryFree _ _)

noncomputable def signPairOn {k : ℕ} (num den : Fin (k+1)) : OracleBlock k :=
  branchPop den (push den false) (push den false) (seq (push den false) (negateOn num))

def signNumerator (a b : ℤ) : ℤ := if b<0 then -a else a

lemma signPairOn_executes {k : ℕ} (g : BitString → ℕ) (num den : Fin (k+1)) (hne : num≠den)
    (s : Store k) (a b : ℤ) (ha : s num=signedBits a) (hb : s den=signedBits b) :
    ∃c,(signPairOn num den).Executes g s
      (Function.update (Function.update s den (signedBits (b.natAbs:ℤ))) num (signedBits (signNumerator a b))) c ∧ c≤10 := by
  have hp : (push den false).Executes g (Function.update s den (Computability.encodeNat b.natAbs))
      (Function.update s den (signedBits (b.natAbs:ℤ))) 1 := by
    convert push_executes g den false (Function.update s den (Computability.encodeNat b.natAbs)) using 1
    simp only [Function.update_self,Function.update_idem,signedBits,negative,
      not_lt.mpr (Int.natCast_nonneg _),decide_false,Int.natAbs_natCast]
  by_cases hn : b<0
  · obtain ⟨c,hc,hcb⟩:=negateOn_executes g num (Function.update s den (signedBits (b.natAbs:ℤ))) a (by simpa [hne] using ha)
    refine ⟨c+5,?_,by omega⟩
    have hh:=branchPop_true den (push den false) (push den false) (seq (push den false) (negateOn num)) g
      (by simpa [signedBits,negative,hn] using hb) (seq_executes _ _ g hp hc)
    simpa [signPairOn,signNumerator,hn,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
  · refine ⟨3,?_,by omega⟩
    have hh:=branchPop_false den (push den false) (push den false) (seq (push den false) (negateOn num)) g
      (by simpa [signedBits,negative,hn] using hb) hp
    have he : Function.update (Function.update s den (signedBits (b.natAbs:ℤ))) num
        (signedBits (signNumerator a b))=Function.update s den (signedBits (b.natAbs:ℤ)) := by
      simp only [signNumerator,hn,ite_false]
      have hnval : (Function.update s den (signedBits (b.natAbs:ℤ))) num=signedBits a := by simpa [hne] using ha
      rw [←hnval]
      exact Function.update_eq_self _ _
    rw [he]
    exact hh

lemma signPairOn_queryFree {k : ℕ} (num den : Fin (k+1)) : (signPairOn num den).QueryFree :=
  branchPop_queryFree _ _ _ _ (push_queryFree _ _) (push_queryFree _ _)
    (seq_queryFree _ _ (push_queryFree _ _) (negateOn_queryFree _))

end HiddenCircuits.Complexity.BinaryArithmetic.RationalNormalize
