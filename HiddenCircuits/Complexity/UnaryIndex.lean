import HiddenCircuits.Complexity.OracleDropFixed
import HiddenCircuits.Complexity.OracleRepeat

/-! Real finite-bit construction of affine shifted unary indices. This is the
address arithmetic used for TM2 ports and their row-offset CNF variables. -/
namespace HiddenCircuits.Complexity.UnaryIndex
open OracleBlock

def state (position base result counter temporary : ℕ) : Store 4 := fun i =>
  List.replicate (if i.val=0 then position else if i.val=1 then base else if i.val=2 then result
    else if i.val=3 then counter else temporary) true

noncomputable def copyBase : OracleBlock 4 := copyOn 1 2 4 (by decide) (by decide) (by decide)
noncomputable def copyPosition : OracleBlock 4 := copyOn 0 3 4 (by decide) (by decide) (by decide)

/-- Constants a,b,scale,offset are part of the fixed program. Data-dependent
position and row base are ordinary unary input strings. -/
noncomputable def build (a b scale offset : ℕ) : OracleBlock 4 :=
  seq copyBase (seq copyPosition (seq (dropFixed 3 a)
    (seq (prepend 3 (List.replicate b true))
      (seq (repeatPrepend 3 2 (List.replicate scale true)) (prepend 2 (List.replicate offset true))))))

theorem build_executes (g : BitString → ℕ) (a b scale offset position base : ℕ) :
    ∃ cost, (build a b scale offset).Executes g (state position base 0 0 0)
      (state position base (base+scale*(position-a+b)+offset) 0 0) cost ∧
      cost ≤ 5*base+5*position+(3*scale+3)*(position-a+b)+2*a+3*b+3*offset+20 := by
  have h₁ : copyBase.Executes g (state position base 0 0 0) (state position base base 0 0) (5*base+2) := by
    have h := copyOn_executes g (1 : Fin 5) 2 4 (by decide) (by decide) (by decide) (state position base 0 0 0) rfl
    convert h using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state]
  have h₂ : copyPosition.Executes g (state position base base 0 0) (state position base base position 0) (5*position+2) := by
    have h := copyOn_executes g (0 : Fin 5) 3 4 (by decide) (by decide) (by decide) (state position base base 0 0) rfl
    convert h using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state]
  obtain ⟨dropCost,hd,hdb⟩ := dropFixed_executes g (3 : Fin 5) a (state position base base position 0)
  have h₃ : (dropFixed (3 : Fin 5) a).Executes g
      (state position base base position 0) (state position base base (position-a) 0) dropCost := by
    convert hd using 1
    funext i;fin_cases i <;> simp [state]
  have h₄ : (prepend (3 : Fin 5) (List.replicate b true)).Executes g
      (state position base base (position-a) 0) (state position base base (position-a+b) 0) (3*b+1) := by
    have h := prepend_executes g (3 : Fin 5) (List.replicate b true) (state position base base (position-a) 0)
    convert h using 1
    · funext i;fin_cases i <;> simp [state,Nat.add_comm]
    · simp
  have h₅ : (repeatPrepend (3 : Fin 5) 2 (List.replicate scale true)).Executes g
      (state position base base (position-a+b) 0)
      (state position base (base+scale*(position-a+b)) 0 0) ((3*scale+3)*(position-a+b)+1) := by
    have h := repeatPrepend_executes g (3 : Fin 5) 2 (by decide) (List.replicate scale true)
      (state position base base (position-a+b) 0)
    convert h using 1
    · funext i;fin_cases i <;> simp [state,Nat.add_comm,Nat.mul_comm]
    · simp [state]
  have h₆ : (prepend (2 : Fin 5) (List.replicate offset true)).Executes g
      (state position base (base+scale*(position-a+b)) 0 0)
      (state position base (base+scale*(position-a+b)+offset) 0 0) (3*offset+1) := by
    have h := prepend_executes g (2 : Fin 5) (List.replicate offset true)
      (state position base (base+scale*(position-a+b)) 0 0)
    convert h using 1
    · funext i;fin_cases i <;> simp [state,Nat.add_comm]
    · simp
  have h := seq_executes _ _ g h₁ (seq_executes _ _ g h₂
    (seq_executes _ _ g h₃ (seq_executes _ _ g h₄ (seq_executes _ _ g h₅ h₆))))
  exact ⟨_,h,by omega⟩

lemma build_queryFree (a b scale offset : ℕ) : (build a b scale offset).QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (dropFixed_queryFree _ _) (seq_queryFree _ _ (prepend_queryFree _ _)
      (seq_queryFree _ _ (repeatPrepend_queryFree _ _ _) (prepend_queryFree _ _)))))

end HiddenCircuits.Complexity.UnaryIndex
