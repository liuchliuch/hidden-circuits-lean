import HiddenCircuits.Circuit.Runtime.SpectralTargetsPure
import HiddenCircuits.Complexity.OracleRepeat

/-! Each target value is emitted by real unary zero/parity checks and fixed pushes. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralTargets
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic

def cellStore (r : ℕ) (mode : Bool) (out copy flag temp : BitString) : Store 5 := fun i =>
  if i.val=0 then List.replicate r true else if i.val=1 then [mode] else if i.val=2 then out
  else if i.val=3 then copy else if i.val=4 then flag else temp
noncomputable def emitConst (z : ℤ) : OracleBlock 5 := prepend 2 (wordChunk (signedBits z)).reverse

 theorem emitConst_executes (g : BitString → ℕ) (z : ℤ) (r : ℕ) (mode : Bool) (out copy flag temp : BitString) :
    (emitConst z).Executes g (cellStore r mode out copy flag temp)
      (cellStore r mode ((wordChunk (signedBits z)).reverse++out) copy flag temp)
      (3*(wordChunk (signedBits z)).length+1) := by
  convert prepend_executes g (2:Fin 6) (wordChunk (signedBits z)).reverse (cellStore r mode out copy flag temp) using 1
  · funext i;fin_cases i <;> simp [cellStore]
  · simp

noncomputable def zeroPositive : OracleBlock 5 := seq (push 0 true) (emitConst 0)
noncomputable def zeroCell : OracleBlock 5 := branchPop 0 (emitConst 1) zeroPositive zeroPositive

theorem zeroCell_executes (g : BitString → ℕ) (r : ℕ) (mode : Bool) (out : BitString) :
    ∃ t, zeroCell.Executes g (cellStore r mode out [] [] [])
      (cellStore r mode ((wordChunk (signedBits ((0:ℤ)^r))).reverse++out) [] [] []) t ∧ t≤21 := by
  cases r with
  | zero =>
    have he := emitConst_executes g 1 0 mode out [] [] []
    have he' : (emitConst 1).Executes g (cellStore 0 mode out [] [] [])
        (cellStore 0 mode ((wordChunk (signedBits 1)).reverse++out) [] [] []) 19 := he
    exact ⟨21,branchPop_empty (0:Fin 6) (emitConst 1) zeroPositive zeroPositive g rfl he',by decide⟩
  | succ r =>
    let s₀ := cellStore (r+1) mode out [] [] []
    let s₁ := cellStore r mode out [] [] []
    have hp : (push (0:Fin 6) true).Executes g s₁ s₀ 1 := by
      convert push_executes g (0:Fin 6) true s₁ using 1
      funext i;fin_cases i <;> simp [s₀,s₁,cellStore,List.replicate_succ]
    have he : (emitConst 0).Executes g s₀
        (cellStore (r+1) mode ((wordChunk (signedBits 0)).reverse++out) [] [] []) 13 := emitConst_executes g 0 (r+1) mode out [] [] []
    have hs : Function.update s₀ (0:Fin 6) (List.replicate r true)=s₁ := by funext i;fin_cases i <;> rfl
    have hh := branchPop_true (0:Fin 6) (emitConst 1) zeroPositive zeroPositive g
      (s:=s₀) (rest:=List.replicate r true) rfl (by rw [hs];exact seq_executes _ _ g hp he)
    refine ⟨18,?_,by decide⟩
    simpa using hh

def parityEmbedding : Fin 2 ↪ Fin 6 where
  toFun i := if i.val=0 then 3 else 4
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
noncomputable def emitParity : OracleBlock 5 := branchPop 4 skip (emitConst 1) (emitConst (-1))
noncomputable def negativeCell : OracleBlock 5 := seq (copyOn 0 3 5 (by decide) (by decide) (by decide))
  (seq (rename parityBlock parityEmbedding) emitParity)

theorem emitParity_executes (g : BitString → ℕ) (r : ℕ) (mode sign : Bool) (out : BitString) :
    emitParity.Executes g (cellStore r mode out [] [sign] [])
      (cellStore r mode ((wordChunk (signedBits (signedNat sign 1))).reverse++out) [] [] []) 21 := by
  have hs : Function.update (cellStore r mode out [] [sign] []) (4:Fin 6) []=cellStore r mode out [] [] [] := by
    funext i;fin_cases i <;> rfl
  cases sign with
  | false =>
    have he : (emitConst 1).Executes g (cellStore r mode out [] [] [])
        (cellStore r mode ((wordChunk (signedBits 1)).reverse++out) [] [] []) 19 := emitConst_executes g 1 r mode out [] [] []
    exact branchPop_false (4:Fin 6) skip (emitConst 1) (emitConst (-1)) g rfl (by rw [hs];exact he)
  | true =>
    have he : (emitConst (-1)).Executes g (cellStore r mode out [] [] [])
        (cellStore r mode ((wordChunk (signedBits (-1))).reverse++out) [] [] []) 19 := emitConst_executes g (-1) r mode out [] [] []
    exact branchPop_true (4:Fin 6) skip (emitConst 1) (emitConst (-1)) g rfl (by rw [hs];exact he)

theorem negativeCell_executes (g : BitString → ℕ) (r : ℕ) (mode : Bool) (out : BitString) :
    negativeCell.Executes g (cellStore r mode out [] [] [])
      (cellStore r mode ((wordChunk (signedBits ((-1:ℤ)^r))).reverse++out) [] [] []) (6*r+29) := by
  let s₀ := cellStore r mode out [] [] []
  let s₁ := cellStore r mode out (List.replicate r true) [] []
  let s₂ := cellStore r mode out [] [parityBit r] []
  have h₁ : (copyOn (0:Fin 6) 3 5 (by decide) (by decide) (by decide)).Executes g s₀ s₁ (5*r+2) := by
    convert copyOn_executes g (0:Fin 6) 3 5 (by decide) (by decide) (by decide) s₀ rfl using 1
    · funext i;fin_cases i <;> simp [s₀,s₁,cellStore]
    · simp [s₀,cellStore]
  have h₂ : (rename parityBlock parityEmbedding).Executes g s₁ s₂ (r+2) := by
    have hh := parityBlock_executes g (List.replicate r true) []
    simp only [List.length_replicate] at hh
    apply rename_executes_to parityBlock parityEmbedding g hh
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro j hj;fin_cases j <;> first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl)
  have h₃ := emitParity_executes g r mode (parityBit r) out
  rw [signedNat_parity] at h₃
  convert seq_executes _ _ g h₁ (seq_executes _ _ g h₂ h₃) using 1 <;> omega

noncomputable def cell : OracleBlock 5 := branchPop 1 skip
  (seq (push 1 false) zeroCell) (seq (push 1 true) negativeCell)

theorem cell_executes (g : BitString → ℕ) (r : ℕ) (mode : Bool) (out : BitString) :
    ∃ t, cell.Executes g (cellStore r mode out [] [] [])
      (cellStore r mode ((wordChunk (signedBits ((base mode)^r))).reverse++out) [] [] []) t ∧ t≤6*r+34 := by
  have hp : (push (1:Fin 6) mode).Executes g (Function.update (cellStore r mode out [] [] []) (1:Fin 6) [])
      (cellStore r mode out [] [] []) 1 := by
    convert push_executes g (1:Fin 6) mode (Function.update (cellStore r mode out [] [] []) (1:Fin 6) []) using 1
    funext i;fin_cases i <;> rfl
  cases mode with
  | false =>
    obtain ⟨t,ht,hb⟩ := zeroCell_executes g r false out
    exact ⟨1+t+2+2,branchPop_false (1:Fin 6) skip _ _ g rfl (seq_executes _ _ g hp ht),by omega⟩
  | true =>
    have ht := negativeCell_executes g r true out
    exact ⟨1+(6*r+29)+2+2,branchPop_true (1:Fin 6) skip _ _ g rfl (seq_executes _ _ g hp ht),by omega⟩

theorem emitConst_queryFree (z : ℤ) : (emitConst z).QueryFree := prepend_queryFree _ _
theorem cell_queryFree : cell.QueryFree :=
  branchPop_queryFree _ _ _ _ skip_queryFree
    (seq_queryFree _ _ (push_queryFree _ _) (branchPop_queryFree _ _ _ _ (emitConst_queryFree _)
      (seq_queryFree _ _ (push_queryFree _ _) (emitConst_queryFree _))
      (seq_queryFree _ _ (push_queryFree _ _) (emitConst_queryFree _))))
    (seq_queryFree _ _ (push_queryFree _ _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
      (seq_queryFree _ _ (rename_queryFree _ _ parityBlock_queryFree)
        (branchPop_queryFree _ _ _ _ skip_queryFree (emitConst_queryFree _) (emitConst_queryFree _)))))
end HiddenCircuits.Circuit.Runtime.SpectralTargets
