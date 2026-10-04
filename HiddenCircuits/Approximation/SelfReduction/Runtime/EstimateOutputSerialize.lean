import HiddenCircuits.Approximation.SelfReduction.Runtime.EstimateOutputPower
import HiddenCircuits.Approximation.SelfReduction.Runtime.ContextPrepare
import HiddenCircuits.Approximation.SelfReduction.Arithmetic

/-! Signed prefixes, predecessor subtraction and rational pairing are all real
bit instructions. The denominator word represents b-1, as decodeEstimate needs. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.EstimateOutput
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic Polynomial

noncomputable def popBit {k : ℕ} (port : Fin (k+1)) : OracleBlock k := branchPop port skip skip skip
 theorem popBit_executes {k : ℕ} (g : BitString → ℕ) (port : Fin (k+1)) (s : Store k)
    (b : Bool) (word : BitString) (hs : s port=b::word) :
    (popBit port).Executes g s (Function.update s port word) 3 := by
  cases b
  · exact branchPop_false _ _ _ _ g hs (skip_executes g _)
  · exact branchPop_true _ _ _ _ g hs (skip_executes g _)
 theorem popBit_queryFree {k : ℕ} (port : Fin (k+1)) : (popBit port).QueryFree :=
  branchPop_queryFree _ _ _ _ skip_queryFree skip_queryFree skip_queryFree

def ratioStore (num den one tmp flag : BitString) : Store 4 := fun i =>
  if i.val=0 then num else if i.val=1 then den else if i.val=2 then one else if i.val=3 then tmp else flag

def subtractionPorts : Fin 4 ↪ Fin 5 where
  toFun i := i.natAdd 1
  inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; simp at this; omega

noncomputable def serialize : OracleBlock 4 := seq (popBit 0) (seq (popBit 1)
  (seq (push 2 true) (seq (rename subBlock subtractionPorts)
  (seq (clear 4) (seq (pairEmit 0 1 2 (by decide) (by decide))
    (moveOn 1 0 2 (by decide) (by decide) (by decide)))))))
noncomputable def serializeTime : Polynomial ℕ := 40*X+50

 theorem serialize_executes (g : BitString → ℕ) (a b : ℕ) (hb : 0<b) :
    ∃ t, serialize.Executes g (ratioStore (signedBits (a:ℤ)) (signedBits (b:ℤ)) [] [] [])
      (clean (encodeRatio a b)) t ∧
      t≤serializeTime.eval ((signedBits (a:ℤ)).length+(signedBits (b:ℤ)).length) := by
  let A := Computability.encodeNat a
  let B := Computability.encodeNat b
  let D := Computability.encodeNat (b-1)
  let s0 := ratioStore (signedBits (a:ℤ)) (signedBits (b:ℤ)) [] [] []
  let s1 := ratioStore A (signedBits (b:ℤ)) [] [] []
  let s2 := ratioStore A B [] [] []
  let s3 := ratioStore A B [true] [] []
  let s4 := ratioStore A D [] [] [false]
  let s5 := ratioStore A D [] [] []
  let s6 := ratioStore [] (pairBits A D) [] [] []
  have h1 : (popBit (0:Fin 5)).Executes g s0 s1 3 := by
    convert popBit_executes g (0:Fin 5) s0 false A (signedBits_nat a) using 1
    funext i; fin_cases i <;> rfl
  have h2 : (popBit (1:Fin 5)).Executes g s1 s2 3 := by
    convert popBit_executes g (1:Fin 5) s1 false B (signedBits_nat b) using 1
    funext i; fin_cases i <;> rfl
  have h3 : (push (2:Fin 5) true).Executes g s2 s3 1 := by
    convert push_executes g (2:Fin 5) true s2 using 1
    funext i; fin_cases i <;> rfl
  have h4 : (rename subBlock subtractionPorts).Executes g s3 s4 (subCost B [true]) := by
    have h := subBlock_encode g b 1
    have hb' : ¬b<1 := by omega
    simp only [hb',decide_false] at h
    apply rename_executes_to subBlock subtractionPorts g h
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
    · intro i hi
      fin_cases i
      · rfl
      · exact False.elim (hi 0 rfl)
      · exact False.elim (hi 1 rfl)
      · exact False.elim (hi 2 rfl)
      · exact False.elim (hi 3 rfl)
  have h5 : (clear (4:Fin 5)).Executes g s4 s5 2 := by
    convert clear_executes g (4:Fin 5) s4 using 1
    funext i; fin_cases i <;> rfl
  have h6 : (pairEmit (0:Fin 5) 1 2 (by decide) (by decide)).Executes g s5 s6 (8*A.length+7) := by
    convert pairEmit_executes g (0:Fin 5) 1 2 (by decide) (by decide) (by decide) s5 rfl using 1
    funext i; fin_cases i <;> rfl
  have h7 : (moveOn (1:Fin 5) 0 2 (by decide) (by decide) (by decide)).Executes g s6
      (clean (encodeRatio a b)) (6*(pairBits A D).length+5) := by
    convert moveOn_executes g (1:Fin 5) 0 2 (by decide) (by decide) (by decide) s6 rfl using 1
    funext i; fin_cases i <;> simp [clean,s6,ratioStore,encodeRatio,Nat.ne_of_gt hb,A,D]
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3
    (seq_executes _ _ g h4 (seq_executes _ _ g h5 (seq_executes _ _ g h6 h7))))),?_⟩
  have hd : D.length≤B.length := by
    dsimp [D,B]
    rw [encodeNat_length,encodeNat_length]
    exact Nat.size_le_size (Nat.sub_le _ _)
  have hc := subCost_bound B [true]
  simp only [List.length_cons,List.length_nil] at hc
  have hm : max B.length 1≤B.length+1 := Nat.max_le.mpr ⟨by omega,by omega⟩
  have hc' : subCost B [true]≤5*(B.length+1)+4 := hc.trans (by omega)
  simp only [serializeTime,eval_add,eval_mul,eval_X,eval_ofNat,signedBits_nat,List.length_cons,pairBits_length]
  change 3+(3+(1+(subCost B [true]+(2+(8*A.length+7+(6*(2*A.length+D.length+1)+5)+2)+2)+2)+2)+2)+2≤_
  dsimp [A,B] at *
  omega

 theorem serialize_queryFree : serialize.QueryFree := seq_queryFree _ _ (popBit_queryFree _)
  (seq_queryFree _ _ (popBit_queryFree _) (seq_queryFree _ _ (push_queryFree _ _)
    (seq_queryFree _ _ (rename_queryFree _ _ subBlock_queryFree)
    (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (pairEmit_queryFree _ _ _ _ _)
      (moveOn_queryFree _ _ _ _ _ _))))))

end HiddenCircuits.Approximation.SelfReduction.Runtime.EstimateOutput
