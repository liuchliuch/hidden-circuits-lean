import HiddenCircuits.DH.Runtime.ScalarCoefficient
import HiddenCircuits.Complexity.GraphVerifier.ReadOnlyAtLeast

/-! Physical unary tests make the crossing producer
total: out-of-range binomial coefficients return their actual value zero,
before the exact-division subroutine can be reached. -/
namespace HiddenCircuits.DH.Runtime.ScalarCoefficient
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic Polynomial

def guardMap (src : Fin 2) : Fin 6↪Fin 26 where
  toFun q:=if q.val=0 then ⟨src.val,by omega⟩ else if q.val=1 then 2 else ⟨q.val+4,by omega⟩
  inj':=by fin_cases src <;> decide +kernel
noncomputable def check (src : Fin 2) : OracleBlock 25:=GraphVerifier.Runtime.readAtLeastOn (guardMap src)
noncomputable def zero : OracleBlock 25:=push 5 false
noncomputable def secondGuard : OracleBlock 25:=seq (check 1) (branchPop 6 zero zero program)
noncomputable def guarded : OracleBlock 25:=seq (check 0) (branchPop 6 zero zero secondGuard)
noncomputable def guardedTime : Polynomial ℕ:=time+100*(X+1)

lemma check_executes (g : BitString→ ℕ) (i j r A B : ℕ) (src : Fin 2) :
    ∃t,(check src).Executes g (store i j r A B [])
      (Function.update (store i j r A B []) 6 [decide (r≤ if src.val=0 then i else j)]) t ∧
      t≤ 13*(i+j+r)+23 := by
  obtain ⟨t,ht,hb⟩:=GraphVerifier.Runtime.readAtLeastOn_executes (guardMap src) g (store i j r A B [])
    (List.replicate (if src.val=0 then i else j) true) (List.replicate r true) (by
      funext q;fin_cases src <;> fin_cases q <;> rfl)
  refine ⟨t,?_,?_⟩
  · simpa only [List.length_replicate] using ht
  · simp only [List.length_replicate] at hb
    split_ifs at hb <;> omega
lemma zero_executes (g : BitString→ ℕ) (i j r A B : ℕ) :
    zero.Executes g (store i j r A B []) (store i j r A B (signedBits (0:ℤ))) 1 := by
  convert push_executes g (5:Fin 26) false (store i j r A B []) using 1
  funext q;fin_cases q <;> rfl
lemma pop_guard (i j r A B : ℕ) (b : Bool) :
    Function.update (Function.update (store i j r A B []) 6 [b]) 6 []=store i j r A B [] := by
  funext q;fin_cases q <;> rfl
lemma guarded_word_zero (i j r A B : ℕ) (h : ¬(r≤ i ∧ r≤ j)) :
    A*B*(i.choose r*j.choose r*r.factorial)=0 := by
  by_cases hi:r≤ i
  · have hj:j<r:=by omega
    simp [Nat.choose_eq_zero_of_lt hj]
  · have hi':i<r:=by omega
    simp [Nat.choose_eq_zero_of_lt hi']

theorem secondGuard_executes (g : BitString→ ℕ) (i j r A B : ℕ) (hi:r≤ i) :
    ∃t,secondGuard.Executes g (store i j r A B [])
      (store i j r A B (signedBits (A*B*(i.choose r*j.choose r*r.factorial):ℕ))) t ∧
      t≤ time.eval (inputSize i j r A B)+13*(i+j+r)+28 := by
  obtain ⟨c,hc,hcb⟩:=check_executes g i j r A B 1
  change (check 1).Executes g (store i j r A B []) (Function.update (store i j r A B []) 6 [decide (r≤ j)]) c at hc
  by_cases hj:r≤ j
  · obtain ⟨t,ht,htb⟩:=executes g i j r A B hi hj
    have hb: (branchPop (6:Fin 26) zero zero program).Executes g
        (Function.update (store i j r A B []) 6 [true])
        (store i j r A B (signedBits (A*B*(i.choose r*j.choose r*r.factorial):ℕ))) (t+2):=by
      apply branchPop_true _ _ _ _ g (rest:=[]) rfl
      rw [pop_guard]
      exact ht
    simp only [hj,decide_true] at hc
    exact ⟨_,seq_executes _ _ g hc hb,by omega⟩
  · have he:=guarded_word_zero i j r A B (by omega)
    have hb: (branchPop (6:Fin 26) zero zero program).Executes g
        (Function.update (store i j r A B []) 6 [false]) (store i j r A B (signedBits (0:ℤ))) 3:=by
      apply branchPop_false _ _ _ _ g (rest:=[]) rfl
      rw [pop_guard]
      exact zero_executes g i j r A B
    simp only [hj,decide_false] at hc
    rw [he]
    exact ⟨_,seq_executes _ _ g hc hb,by omega⟩

theorem guarded_executes (g : BitString→ ℕ) (i j r A B : ℕ) :
    ∃t,guarded.Executes g (store i j r A B [])
      (store i j r A B (signedBits (A*B*(i.choose r*j.choose r*r.factorial):ℕ))) t ∧
      t≤ guardedTime.eval (inputSize i j r A B) := by
  obtain ⟨c,hc,hcb⟩:=check_executes g i j r A B 0
  change (check 0).Executes g (store i j r A B []) (Function.update (store i j r A B []) 6 [decide (r≤ i)]) c at hc
  by_cases hi:r≤ i
  · obtain ⟨t,ht,htb⟩:=secondGuard_executes g i j r A B hi
    have hb:(branchPop (6:Fin 26) zero zero secondGuard).Executes g
        (Function.update (store i j r A B []) 6 [true])
        (store i j r A B (signedBits (A*B*(i.choose r*j.choose r*r.factorial):ℕ))) (t+2):=by
      apply branchPop_true _ _ _ _ g (rest:=[]) rfl
      rw [pop_guard]
      exact ht
    simp only [hi,decide_true] at hc
    refine ⟨_,seq_executes _ _ g hc hb,?_⟩
    simp only [guardedTime,eval_add,eval_mul,eval_X,eval_ofNat,eval_one]
    unfold inputSize at *;omega
  · have he:=guarded_word_zero i j r A B (by omega)
    have hb:(branchPop (6:Fin 26) zero zero secondGuard).Executes g
        (Function.update (store i j r A B []) 6 [false]) (store i j r A B (signedBits (0:ℤ))) 3:=by
      apply branchPop_false _ _ _ _ g (rest:=[]) rfl
      rw [pop_guard]
      exact zero_executes g i j r A B
    simp only [hi,decide_false] at hc
    rw [he]
    refine ⟨_,seq_executes _ _ g hc hb,?_⟩
    simp only [guardedTime,eval_add,eval_mul,eval_X,eval_ofNat,eval_one]
    unfold inputSize at *;omega
lemma guarded_queryFree : guarded.QueryFree:=seq_queryFree _ _ (GraphVerifier.Runtime.readAtLeastOn_queryFree _)
  (branchPop_queryFree _ _ _ _ (push_queryFree _ _) (push_queryFree _ _)
    (seq_queryFree _ _ (GraphVerifier.Runtime.readAtLeastOn_queryFree _)
      (branchPop_queryFree _ _ _ _ (push_queryFree _ _) (push_queryFree _ _) queryFree)))
noncomputable def on {l : ℕ} (φ : Fin 26↪Fin (l+1)) : OracleBlock l:=rename guarded φ
lemma on_executes {l : ℕ} (φ : Fin 26↪Fin (l+1)) (g : BitString→ ℕ) (s : Store l)
    (i j r A B : ℕ) (hs:s∘φ=store i j r A B []) :
    ∃t,(on φ).Executes g s
      (Function.update s (φ 5) (signedBits (A*B*(i.choose r*j.choose r*r.factorial):ℕ))) t ∧
      t≤ guardedTime.eval (inputSize i j r A B) := by
  obtain ⟨t,ht,hb⟩:=guarded_executes g i j r A B
  refine ⟨t,?_,hb⟩
  apply rename_executes_to _ φ g ht hs
  · have he:(Function.update s (φ 5) (signedBits (A*B*(i.choose r*j.choose r*r.factorial):ℕ)))∘φ=
        Function.update (s∘φ) 5 (signedBits (A*B*(i.choose r*j.choose r*r.factorial):ℕ)):=by
      funext q;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext q;fin_cases q <;> rfl
  · intro q hq;exact Function.update_of_ne (hq 5).symm _ _
lemma on_queryFree {l : ℕ} (φ : Fin 26↪Fin (l+1)) : (on φ).QueryFree:=rename_queryFree _ _ guarded_queryFree
end HiddenCircuits.DH.Runtime.ScalarCoefficient
