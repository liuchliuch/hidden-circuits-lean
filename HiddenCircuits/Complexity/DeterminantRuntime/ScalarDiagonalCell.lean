import HiddenCircuits.Complexity.DeterminantRuntime.ScalarDiagonalRead
import HiddenCircuits.Complexity.DeterminantRuntime.IdentityMatrix
import HiddenCircuits.Complexity.BinaryArithmetic.Operations

/-! Fresh reconstruction: diagonal test and an actual framed signed addition. -/
namespace HiddenCircuits.Complexity.DeterminantRuntime.ScalarDiagonal
open OracleBlock BinaryArithmetic GraphVerifier.Runtime MatrixProduct
set_option maxHeartbeats 900000

def addEmbedding : Fin 9 ↪ Fin 25 where
  toFun i := ![3,11,10,12,13,14,15,16,17] i
  inj' := by decide +kernel
noncomputable def addScalar : OracleBlock 24 :=
  seq (copyOn 9 11 12 (by decide) (by decide) (by decide)) (rename Operation.add.program addEmbedding)
noncomputable def select : OracleBlock 24 := branchPop 10 skip skip addScalar
noncomputable def modifyCell : OracleBlock 24 := seq (readLengthOn IdentityMatrix.comparison) select
noncomputable def cell : OracleBlock 24 := seq readCell modifyCell

lemma addScalar_executes (g : BitString → ℕ) (n i j : ℕ) (out inner outer a : BitString) (x c : ℤ) :
    ∃t,addScalar.Executes g (base n i j (signedBits x) out inner outer a (signedBits c))
      (base n i j (signedBits (x+c)) out inner outer a (signedBits c)) t ∧
      t ≤ 5*(signedBits c).length+operationTime.eval ((signedBits x).length+(signedBits c).length)+4 := by
  let s := base n i j (signedBits x) out inner outer a (signedBits c)
  let s1 := Function.update s (11:Fin 25) (signedBits c)
  have h1 : (copyOn (9:Fin 25) 11 12 (by decide) (by decide) (by decide)).Executes g s s1 (5*(signedBits c).length+2) := by
    simpa [s1,s,base,cellState] using copyOn_executes g (9:Fin 25) 11 12 (by decide) (by decide) (by decide) s rfl
  obtain ⟨t,ht,htb⟩ := Operation.add.executes g x c trivial
  have h2 : (rename Operation.add.program addEmbedding).Executes g s1
      (base n i j (signedBits (x+c)) out inner outer a (signedBits c)) t := by
    apply rename_executes_to Operation.add.program addEmbedding g ht
    · funext r;fin_cases r <;> rfl
    · funext r;fin_cases r <;> rfl
    · intro r hr
      have h3 : r.val≠3 := by intro h;exact hr 0 (Fin.ext h.symm)
      have h11 : r≠(11:Fin 25) := by intro h;subst r;exact hr 1 rfl
      simp only [s1,Function.update_of_ne h11,s,base,cellState,h3,if_false]
  exact ⟨_,seq_executes _ _ g h1 h2,by omega⟩

lemma select_executes (g : BitString → ℕ) (n i j : ℕ) (out inner outer a : BitString) (x c : ℤ) :
    ∃t,select.Executes g
      (Function.update (base n i j (signedBits x) out inner outer a (signedBits c)) 10 [decide (i=j)])
      (base n i j (signedBits (if i=j then x+c else x)) out inner outer a (signedBits c)) t ∧
      t ≤ 5*(signedBits c).length+operationTime.eval ((signedBits x).length+(signedBits c).length)+6 := by
  let s := base n i j (signedBits x) out inner outer a (signedBits c)
  have he : Function.update (Function.update s (10:Fin 25) [decide (i=j)]) 10 []=s := by
    rw [Function.update_idem]
    exact Function.update_eq_self _ _
  dsimp only [s] at he
  by_cases h:i=j
  · obtain ⟨t,ht,hb⟩ := addScalar_executes g n i j out inner outer a x c
    refine ⟨t+2,?_,by omega⟩
    apply branchPop_true (10:Fin 25) skip skip addScalar g (rest:=[]) (by simp [h])
    simpa only [he,if_pos h] using ht
  · refine ⟨3,?_,by omega⟩
    apply branchPop_false (10:Fin 25) skip skip addScalar g (rest:=[]) (by simp [h])
    simpa only [he,if_neg h] using skip_executes g s

lemma modifyCell_executes (g : BitString → ℕ) (n i j : ℕ) (out inner outer a : BitString) (x c : ℤ) :
    ∃t,modifyCell.Executes g (base n i j (signedBits x) out inner outer a (signedBits c))
      (base n i j (signedBits (if i=j then x+c else x)) out inner outer a (signedBits c)) t ∧
      t ≤ 13*(i+j)+5*(signedBits c).length+operationTime.eval ((signedBits x).length+(signedBits c).length)+31 := by
  let s := base n i j (signedBits x) out inner outer a (signedBits c)
  obtain ⟨t,ht,hb⟩ := readLengthOn_executes IdentityMatrix.comparison g s (List.replicate i true) (List.replicate j true)
    (by funext r;fin_cases r <;> rfl)
  simp only [List.length_replicate] at ht hb
  obtain ⟨u,hu,hub⟩ := select_executes g n i j out inner outer a x c
  exact ⟨_,seq_executes _ _ g ht hu,by omega⟩

lemma cell_queryFree : cell.QueryFree := seq_queryFree _ _ readCell_queryFree
  (seq_queryFree _ _ (readLengthOn_queryFree _) (branchPop_queryFree _ _ _ _ skip_queryFree skip_queryFree
    (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (rename_queryFree _ _ Operation.add.queryFree))))
end HiddenCircuits.Complexity.DeterminantRuntime.ScalarDiagonal
