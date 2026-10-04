import HiddenCircuits.Complexity.BinaryArithmetic.GcdRuntime
import HiddenCircuits.Complexity.BinaryArithmetic.RegisterMachine

/-! Sign erasure and the exact Euclidean gcd as a clean signed-register operation. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic.Gcd
open OracleBlock Polynomial

noncomputable def discardSign {k : ℕ} (i : Fin (k+1)) (B : OracleBlock k) : OracleBlock k :=
  branchPop i B B B
lemma discardSign_executes {k : ℕ} (i : Fin (k+1)) (B : OracleBlock k)
    (g : BitString → ℕ) (s t : Store k) (b : Bool) (bs : BitString) (c : ℕ)
    (hs : s i=b::bs) (h : B.Executes g (Function.update s i bs) t c) :
    (discardSign i B).Executes g s t (c+2) := by
  cases b
  · exact branchPop_false _ _ _ _ g hs h
  · exact branchPop_true _ _ _ _ g hs h
lemma discardSign_queryFree {k : ℕ} (i : Fin (k+1)) (B : OracleBlock k) (h : B.QueryFree) :
    (discardSign i B).QueryFree := branchPop_queryFree _ _ _ _ h h h

noncomputable def signedProgram : OracleBlock 8 :=
  discardSign 0 (discardSign 1 (seq program (push 0 false)))
noncomputable def signedTime : Polynomial ℕ := time+7

theorem signedProgram_executes (g : BitString → ℕ) (a b : ℤ) :
    ∃t,signedProgram.Executes g (binaryStore (signedBits a) (signedBits b))
      (binaryStore (signedBits (Nat.gcd a.natAbs b.natAbs : ℤ)) []) t ∧
      t≤signedTime.eval ((signedBits a).length+(signedBits b).length) := by
  obtain ⟨c,hc,hbound⟩:=binary_executes g a.natAbs b.natAbs
  have hp : (push (0:Fin 9) false).Executes g
      (binaryStore (Computability.encodeNat (Nat.gcd a.natAbs b.natAbs)) [])
      (binaryStore (signedBits (Nat.gcd a.natAbs b.natAbs:ℤ)) []) 1 := by
    convert push_executes g (0:Fin 9) false _ using 1
    funext i;fin_cases i <;> simp [binaryStore,signedBits,negative]
  have h0 : Function.update (binaryStore (signedBits a) (signedBits b)) (0:Fin 9)
      (Computability.encodeNat a.natAbs)=binaryStore (Computability.encodeNat a.natAbs) (signedBits b) := by
    funext i;fin_cases i <;> rfl
  have h1 : Function.update (binaryStore (Computability.encodeNat a.natAbs) (signedBits b)) (1:Fin 9)
      (Computability.encodeNat b.natAbs)=binaryStore (Computability.encodeNat a.natAbs) (Computability.encodeNat b.natAbs) := by
    funext i;fin_cases i <;> rfl
  refine ⟨c+7,?_,?_⟩
  · have hh:=discardSign_executes (1:Fin 9) _ g
      (binaryStore (Computability.encodeNat a.natAbs) (signedBits b)) _ (negative b)
      (Computability.encodeNat b.natAbs) (c+3) rfl
      (by rw [h1];exact seq_executes _ _ g hc hp)
    have hh':=discardSign_executes (0:Fin 9) _ g
      (binaryStore (signedBits a) (signedBits b)) _ (negative a)
      (Computability.encodeNat a.natAbs) (c+3+2) rfl (by rw [h0];exact hh)
    convert hh' using 1 <;> omega
  · have hm:=polynomial_nat_eval_mono time
      (show (Computability.encodeNat a.natAbs).length+(Computability.encodeNat b.natAbs).length≤
        (signedBits a).length+(signedBits b).length by simp only [signedBits,List.length_cons];omega)
    dsimp only at hm
    simp only [signedTime,eval_add,eval_ofNat]
    omega

lemma signedProgram_queryFree : signedProgram.QueryFree :=
  discardSign_queryFree _ _ (discardSign_queryFree _ _ (seq_queryFree _ _ program_queryFree (push_queryFree _ _)))

end HiddenCircuits.Complexity.BinaryArithmetic.Gcd

namespace HiddenCircuits.Complexity.BinaryArithmetic.RegisterMachine
open OracleBlock

noncomputable def assignBlock (B : OracleBlock 8) (d i j : Fin 7) : OracleBlock 15 :=
  seq (readLeft i) (seq (readRight j) (seq (rename B workPort) (writeResult d)))

theorem assignBlock_executes (g : BitString → ℕ) (B : OracleBlock 8) (d i j : Fin 7)
    (R : Fin 7 → BitString) (z : BitString) (c : ℕ)
    (hB : B.Executes g (binaryStore (R i) (R j)) (binaryStore z []) c) :
    (assignBlock B d i j).Executes g (store [] [] R) (store [] [] (Function.update R d z))
      (5*(R i).length+5*(R j).length+c+(R d).length+6*z.length+18) := by
  have hb : (rename B workPort).Executes g (store (R i) (R j) R) (store z [] R) c := by
    apply rename_executes_to B workPort g hB
    · funext q;exact store_work _ _ _ q
    · funext q;exact store_work _ _ _ q
    · intro q hq
      have hn : 9≤q.val := by
        by_contra hh
        exact hq ⟨q.val,by omega⟩ (Fin.ext rfl)
      simp [store,show q.val≠0 by omega,show q.val≠1 by omega]
  convert seq_executes _ _ g (readLeft_executes g i R)
    (seq_executes _ _ g (readRight_executes g j (R i) R)
      (seq_executes _ _ g hb (writeResult_executes g d z R))) using 1 <;> omega

lemma assignBlock_queryFree (B : OracleBlock 8) (d i j : Fin 7) (h : B.QueryFree) :
    (assignBlock B d i j).QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _
    (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (rename_queryFree _ _ h)
      (seq_queryFree _ _ (clear_queryFree _) (moveOn_queryFree _ _ _ _ _ _))))

end HiddenCircuits.Complexity.BinaryArithmetic.RegisterMachine
