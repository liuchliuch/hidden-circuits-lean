import HiddenCircuits.Complexity.BinaryArithmetic.RationalSignRuntime
import HiddenCircuits.Complexity.PairSerialization

/-! Register-level Euclidean normalization: the gcd is computed, then both exact
quotients are physically produced, sign-normalized, paired, and cleaned. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic.RationalNormalize
open OracleBlock Polynomial

def regs (a b d : BitString) : Fin 7 → BitString := fun i =>
  if i.val=0 then a else if i.val=1 then b else if i.val=2 then d else []
def regState (a b d : BitString) : Store 15 := RegisterMachine.store [] [] (regs a b d)

noncomputable def gcdAssign : OracleBlock 15 := RegisterMachine.assignBlock Gcd.signedProgram 2 0 1
noncomputable def numAssign : OracleBlock 15 := RegisterMachine.assignBlock cleanDivide 0 0 2
noncomputable def denAssign : OracleBlock 15 := RegisterMachine.assignBlock cleanDivide 1 1 2
noncomputable def arithmetic : OracleBlock 15 := seq gcdAssign (seq numAssign denAssign)
noncomputable def arithmeticTime : Polynomial ℕ :=
  Gcd.signedTime.comp (2*X)+2*cleanDivideTime.comp (2*X)+60*X+60

lemma regs_update_zero (a b d z : BitString) : Function.update (regs a b d) (0:Fin 7) z=regs z b d := by
  funext i;fin_cases i <;> rfl
lemma regs_update_one (a b d z : BitString) : Function.update (regs a b d) (1:Fin 7) z=regs a z d := by
  funext i;fin_cases i <;> rfl
lemma regs_update_two (a b d z : BitString) : Function.update (regs a b d) (2:Fin 7) z=regs a b z := by
  funext i;fin_cases i <;> rfl

/-- Internal arithmetic contract; divisibility below is discharged from gcd in
the public rational-normalization theorem. -/
theorem arithmetic_executes (g : BitString → ℕ) (a b : ℤ)
    (d : ℤ) (hd : d=(Nat.gcd a.natAbs b.natAbs:ℤ))
    (hd0 : d≠0) (hda : d∣a) (hdb : d∣b) (L : ℕ)
    (haL : (signedBits a).length≤L) (hbL : (signedBits b).length≤L)
    (hdL : (signedBits d).length≤L) (hqL : (signedBits (a/d)).length≤L)
    (hrL : (signedBits (b/d)).length≤L) :
    ∃c,arithmetic.Executes g (regState (signedBits a) (signedBits b) [])
      (regState (signedBits (a/d)) (signedBits (b/d)) (signedBits d)) c ∧
      c≤arithmeticTime.eval L := by
  obtain ⟨cg,hg,hgb⟩:=Gcd.signedProgram_executes g a b
  rw [←hd] at hg
  have h1:=RegisterMachine.assignBlock_executes g Gcd.signedProgram 2 0 1
    (regs (signedBits a) (signedBits b) []) (signedBits d) cg hg
  rw [regs_update_two] at h1
  obtain ⟨cn,hn,hnb⟩:=cleanDivide_executes g a d hd0 hda
  have h2:=RegisterMachine.assignBlock_executes g cleanDivide 0 0 2
    (regs (signedBits a) (signedBits b) (signedBits d)) (signedBits (a/d)) cn hn
  rw [regs_update_zero] at h2
  obtain ⟨cd,hden,hdenb⟩:=cleanDivide_executes g b d hd0 hdb
  have h3:=RegisterMachine.assignBlock_executes g cleanDivide 1 1 2
    (regs (signedBits (a/d)) (signedBits b) (signedBits d)) (signedBits (b/d)) cd hden
  rw [regs_update_one] at h3
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 h3),?_⟩
  have bg:=polynomial_nat_eval_mono Gcd.signedTime (show (signedBits a).length+(signedBits b).length≤2*L by omega)
  have bn:=polynomial_nat_eval_mono cleanDivideTime (show (signedBits a).length+(signedBits d).length≤2*L by omega)
  have bd:=polynomial_nat_eval_mono cleanDivideTime (show (signedBits b).length+(signedBits d).length≤2*L by omega)
  dsimp only at bg bn bd
  simp [regs]
  simp only [arithmeticTime,eval_add,eval_mul,eval_ofNat,eval_X,eval_comp]
  omega

lemma arithmetic_queryFree : arithmetic.QueryFree :=
  seq_queryFree _ _ (RegisterMachine.assignBlock_queryFree _ _ _ _ Gcd.signedProgram_queryFree)
    (seq_queryFree _ _ (RegisterMachine.assignBlock_queryFree _ _ _ _ cleanDivide_queryFree)
      (RegisterMachine.assignBlock_queryFree _ _ _ _ cleanDivide_queryFree))

def pairMap : Fin 3 ↪ Fin 16 where
  toFun i := if i.val=0 then 10 else if i.val=1 then 9 else 2
  inj' := by decide +kernel
noncomputable def serialize : OracleBlock 15 := PairSerialization.on pairMap
noncomputable def finish : OracleBlock 15 :=
  seq (signPairOn 9 10) (seq serialize (cleanResult 10 2 (by decide) (by decide)))
noncomputable def program : OracleBlock 15 := seq arithmetic finish
noncomputable def time : Polynomial ℕ := arithmeticTime+300*X+200

lemma pair_length (a b : BitString) : (pairBits a b).length=2*a.length+1+b.length := by
  induction a with
  | nil => simp [pairBits];omega
  | cons bit bs ih => simp [pairBits,ih];omega
lemma signedBits_neg_length (a : ℤ) : (signedBits (-a)).length=(signedBits a).length := by simp [signedBits]
lemma signedBits_natAbs_length (a : ℤ) : (signedBits (a.natAbs:ℤ)).length=(signedBits a).length := by simp only [signedBits,List.length_cons,Int.natAbs_natCast]
lemma signedBits_signNumerator_length (a b : ℤ) :
    (signedBits (signNumerator a b)).length=(signedBits a).length := by
  unfold signNumerator;split_ifs <;> simp [signedBits]

lemma finish_executes (g : BitString → ℕ) (a b d : ℤ) (L : ℕ)
    (ha : (signedBits a).length≤L) (hb : (signedBits b).length≤L) (hd : (signedBits d).length≤L) :
    ∃c,finish.Executes g (regState (signedBits a) (signedBits b) (signedBits d))
      (Function.update (fun _=>[]) 0 (pairBits (signedBits (signNumerator a b)) (signedBits (b.natAbs:ℤ)))) c ∧
      c≤300*L+198 := by
  obtain ⟨cs,hs,hsb⟩:=signPairOn_executes g (9:Fin 16) 10 (by decide)
    (regState (signedBits a) (signedBits b) (signedBits d)) a b rfl rfl
  have he : Function.update (Function.update (regState (signedBits a) (signedBits b) (signedBits d))
      (10:Fin 16) (signedBits (b.natAbs:ℤ))) 9 (signedBits (signNumerator a b))=
      regState (signedBits (signNumerator a b)) (signedBits (b.natAbs:ℤ)) (signedBits d) := by
    funext i;fin_cases i <;> rfl
  rw [he] at hs
  have hp:=PairSerialization.on_executes pairMap g
    (regState (signedBits (signNumerator a b)) (signedBits (b.natAbs:ℤ)) (signedBits d))
    (signedBits (signNumerator a b)) (signedBits (b.natAbs:ℤ))
    (by funext i;fin_cases i <;> rfl)
  have hpout : Function.update (Function.update
      (regState (signedBits (signNumerator a b)) (signedBits (b.natAbs:ℤ)) (signedBits d))
      (pairMap 1) []) (pairMap 0)
      (pairBits (signedBits (signNumerator a b)) (signedBits (b.natAbs:ℤ)))=
      regState [] (pairBits (signedBits (signNumerator a b)) (signedBits (b.natAbs:ℤ))) (signedBits d) := by
    funext i;fin_cases i <;> rfl
  rw [hpout] at hp
  have hpL : (pairBits (signedBits (signNumerator a b)) (signedBits (b.natAbs:ℤ))).length≤3*L+1 := by
    rw [pair_length,signedBits_signNumerator_length,signedBits_natAbs_length];omega
  obtain ⟨cc,hc,hcb⟩:=cleanResult_executes g (10:Fin 16) 2 (by decide) (by decide) (by decide)
    (regState [] (pairBits (signedBits (signNumerator a b)) (signedBits (b.natAbs:ℤ))) (signedBits d))
    (3*L+1) (by intro i;fin_cases i <;> first | exact hpL | exact hd.trans (by omega) | exact Nat.zero_le _)
  refine ⟨_,seq_executes _ _ g hs (seq_executes _ _ g hp hc),?_⟩
  rw [signedBits_signNumerator_length]
  omega

lemma finish_queryFree : finish.QueryFree := seq_queryFree _ _ (signPairOn_queryFree _ _)
  (seq_queryFree _ _ (PairSerialization.on_queryFree _) (cleanResult_queryFree _ _ _ _))
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ arithmetic_queryFree finish_queryFree

end HiddenCircuits.Complexity.BinaryArithmetic.RationalNormalize
