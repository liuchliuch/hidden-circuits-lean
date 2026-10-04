import HiddenCircuits.GraphReduction.Runtime.DescriptorEvenPositive

namespace HiddenCircuits.GraphReduction.Runtime.DescriptorEven
open Complexity OracleBlock BinaryArithmetic DescriptorFront
set_option maxHeartbeats 700000
noncomputable def select : OracleBlock 19 := branchPop 11 (differenceRow false) positive positive
noncomputable def program : OracleBlock 19 := seq (copyOn 10 11 6 (by decide) (by decide) (by decide)) select

lemma clock_update (v : VertexRecord) (width height samples clock next : ℕ)
    (S T pairs out : BitString) (count : ℕ) :
    Function.update (workState v width height samples clock [] S T pairs out count) 11 (List.replicate next true)=
      workState v width height samples next [] S T pairs out count := by
  funext i;fin_cases i <;> rfl

lemma select_executes (g : BitString → ℕ) (width height samples : ℕ) (S T pairs out : BitString) (count : ℕ)
    (hS : S.length=width) (hT : T.length=width) :
    ∃c,select.Executes g (workState (vertex 0) width height samples height [] S T pairs out count)
      (workState (vertex 0) width height samples 0 [] S T pairs
        ((encodeBitList ((records width height S T).map encodeVertex)).reverse++out) (count+(records width height S T).length)) c ∧
      c≤bound width height+2 := by
  cases height with
  | zero =>
    obtain ⟨c,hc,hb⟩ := differenceRow_executes g false (vertex 0) rfl width 0 samples 0 S T pairs out count (by simpa only [Bool.false_eq_true,ite_false] using hS.trans hT.symm)
    refine ⟨c+2,branchPop_empty 11 (differenceRow false) positive positive g rfl hc,?_⟩
    simp only [Bool.false_eq_true,ite_false,vertex,backgroundCode] at hb
    rw [hS] at hb
    unfold bound
    nlinarith
  | succ n =>
    obtain ⟨c,hc,hb⟩ := positive_executes g width n samples S T pairs out count hS hT
    refine ⟨c+2,?_,by omega⟩
    apply branchPop_true 11 (differenceRow false) positive positive g rfl
    rw [clock_update]
    exact hc

theorem program_executes (g : BitString → ℕ) (width height samples : ℕ) (S T pairs out : BitString) (count : ℕ)
    (hS : S.length=width) (hT : T.length=width) :
    ∃c,program.Executes g (workState (vertex 0) width height samples 0 [] S T pairs out count)
      (workState (vertex 0) width height samples 0 [] S T pairs
        ((encodeBitList ((records width height S T).map encodeVertex)).reverse++out) (count+(records width height S T).length)) c ∧
      c≤bound width height+5*height+6 := by
  have hp : (copyOn (10:Fin 20) 11 6 (by decide) (by decide) (by decide)).Executes g
      (workState (vertex 0) width height samples 0 [] S T pairs out count)
      (workState (vertex 0) width height samples height [] S T pairs out count) (5*height+2) := by
    convert copyOn_executes g (10:Fin 20) 11 6 (by decide) (by decide) (by decide)
      (workState (vertex 0) width height samples 0 [] S T pairs out count) rfl using 1
    · funext i;fin_cases i <;> simp [workState,DescriptorAtom.state]
    · simp [workState]
  obtain ⟨c,hc,hb⟩ := select_executes g width height samples S T pairs out count hS hT
  exact ⟨_,seq_executes _ _ g hp hc,by omega⟩
end HiddenCircuits.GraphReduction.Runtime.DescriptorEven
