import HiddenCircuits.Complexity.DeterminantRuntime.MatrixProductLayout
import HiddenCircuits.DH.Runtime.WordArray
import HiddenCircuits.Complexity.UnaryArithmetic

/-! Fresh reconstruction: actual row-major index arithmetic and read-only word lookup. -/
namespace HiddenCircuits.Complexity.DeterminantRuntime.ScalarDiagonal
open OracleBlock BinaryArithmetic
open MatrixProduct
set_option maxHeartbeats 800000

abbrev base (n i j : ℕ) (word out inner outer a c : BitString) : Store 24 :=
  cellState n i j word out inner outer a c [] [] [] []
noncomputable def indexProgram : OracleBlock 24 := seq (copyOn 1 10 12 (by decide) (by decide) (by decide))
  (seq (repeatCopy 10 0 11 12 (by decide) (by decide) (by decide))
    (copyOn 2 11 12 (by decide) (by decide) (by decide)))
def lookupEmbedding : Fin 8 ↪ Fin 25 where
  toFun i := ![8,11,3,10,12,13,14,15] i
  inj' := by decide +kernel
noncomputable def readCell : OracleBlock 24 := seq indexProgram
  (seq (DH.Runtime.WordArray.readOn lookupEmbedding) (clear 11))

lemma index_executes (g : BitString → ℕ) (n i j : ℕ) (out inner outer a c : BitString) :
    indexProgram.Executes g (base n i j [] out inner outer a c)
      (Function.update (base n i j [] out inner outer a c) 11 (List.replicate (i*n+j) true))
      (5*i+(5*n+4)*i+5*j+9) := by
  let s := base n i j [] out inner outer a c
  let s1 := Function.update s (10:Fin 25) (List.replicate i true)
  let s2 := Function.update s (11:Fin 25) (List.replicate (i*n) true)
  have h1 : (copyOn (1:Fin 25) 10 12 (by decide) (by decide) (by decide)).Executes g s s1 (5*i+2) := by
    simpa [s,s1,base,cellState] using copyOn_executes g (1:Fin 25) 10 12 (by decide) (by decide) (by decide) s rfl
  have h2 : (repeatCopy (10:Fin 25) 0 11 12 (by decide) (by decide) (by decide)).Executes g s1 s2 ((5*n+4)*i+1) := by
    have hh := unaryMultiply_executes g (10:Fin 25) 0 11 12 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) s1 i n (by simp [s1]) rfl rfl
    convert hh using 1
    funext q;fin_cases q <;> simp [s1,s2,s,base,cellState,workStore]
  have h3 : (copyOn (2:Fin 25) 11 12 (by decide) (by decide) (by decide)).Executes g s2
      (Function.update s 11 (List.replicate (i*n+j) true)) (5*j+2) := by
    simpa [s2,s,base,cellState,←List.replicate_add,Nat.add_comm] using
      copyOn_executes g (2:Fin 25) 11 12 (by decide) (by decide) (by decide) s2 rfl
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 h3) using 1 <;> omega

def readBound (n i j L : ℕ) : ℕ :=
  5*i+(5*n+4)*i+5*j+GraphReduction.Runtime.lookupBound L (i*n+j)+(i*n+j)+14

theorem readCell_executes (g : BitString → ℕ) (n i j : ℕ) (ws : List BitString)
    (c out inner outer : BitString) :
    ∃t,readCell.Executes g (base n i j [] out inner outer (encodeBitList ws) c)
      (base n i j (ws[i*n+j]?.getD []) out inner outer (encodeBitList ws) c) t ∧
      t ≤ readBound n i j (encodeBitList ws).length := by
  let s := base n i j [] out inner outer (encodeBitList ws) c
  let s1 := Function.update s (11:Fin 25) (List.replicate (i*n+j) true)
  let s2 := Function.update s1 (3:Fin 25) (ws[i*n+j]?.getD [])
  have h1 := index_executes g n i j out inner outer (encodeBitList ws) c
  obtain ⟨b,h2,hb⟩ := DH.Runtime.WordArray.readOn_executes lookupEmbedding g s1 ws (i*n+j)
    (by funext q;fin_cases q <;> rfl)
  change (DH.Runtime.WordArray.readOn lookupEmbedding).Executes g s1 s2 b at h2
  have h3 : (clear (11:Fin 25)).Executes g s2
      (base n i j (ws[i*n+j]?.getD []) out inner outer (encodeBitList ws) c) (i*n+j+1) := by
    have hh := clear_executes g (11:Fin 25) s2
    have he : Function.update s2 (11:Fin 25) []=
        base n i j (ws[i*n+j]?.getD []) out inner outer (encodeBitList ws) c := by
      funext q;fin_cases q <;> rfl
    rw [he] at hh
    simpa [s2,s1] using hh
  exact ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 h3),by unfold readBound;omega⟩
lemma index_queryFree : indexProgram.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (repeatCopy_queryFree _ _ _ _ _ _ _) (copyOn_queryFree _ _ _ _ _ _))
lemma readCell_queryFree : readCell.QueryFree := seq_queryFree _ _ index_queryFree
  (seq_queryFree _ _ (DH.Runtime.WordArray.readOn_queryFree _) (clear_queryFree _))
end HiddenCircuits.Complexity.DeterminantRuntime.ScalarDiagonal
