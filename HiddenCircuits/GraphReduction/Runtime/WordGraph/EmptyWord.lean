import HiddenCircuits.GraphReduction.Runtime.WordGraph.DriverDimensions
import HiddenCircuits.Complexity.CNFCloneEmitter.WordEquality
import HiddenCircuits.Complexity.BinaryArithmetic.Operations

/-! Fresh reconstruction: empty words are evaluated by an actual destructive
boundary-mask comparison. This branch makes no graph query. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.EmptyWord
open Complexity OracleBlock BinaryArithmetic
set_option maxHeartbeats 800000

def answer (w : WordInstance) : ℤ := if w.source=w.target then 1 else 0
lemma stateBits_injective {n q : ℕ} : Function.Injective (@stateBits n q) := by
  intro S T h
  have hh := congrArg (decodeState n q) h
  simpa only [decodeState_stateBits,Option.some.injEq] using hh
lemma bits_equal (w : WordInstance) : stateBits w.source=stateBits w.target ↔ w.source=w.target :=
  stateBits_injective.eq_iff
lemma answer_value (w : WordInstance) (hw : w.word=[]) : (answer w:ℚ)=w.value := by
  simp only [answer,WordInstance.value,hw,wordMatrix_nil,Matrix.one_apply]
  split_ifs <;> norm_num

def comparison : Fin 3 ↪ Fin 24 where
  toFun i := ![16,17,19] i
  inj' := by decide +kernel
noncomputable def compare : OracleBlock 23 := seq (push 19 true) (rename CNFCloneEmitter.WordEquality.program comparison)
noncomputable def code : OracleBlock 23 := branchPop 19 (push 19 false) (push 19 false)
  (seq (push 19 true) (push 19 false))
noncomputable def evaluate : OracleBlock 23 := seq compare code
noncomputable def afterParse : OracleBlock 23 := seq evaluate (cleanResult 19 20 (by decide) (by decide))

def compared (w : WordInstance) : Store 23 :=
  Function.update (Function.update (Function.update (DriverDimensions.state w 0 0 0) 16 []) 17 []) 19
    [decide (stateBits w.source=stateBits w.target)]

theorem compare_executes (g : BitString → ℕ) (w : WordInstance) :
    ∃c,compare.Executes g (DriverDimensions.state w 0 0 0) (compared w) c ∧ c≤40*w.particles+16 := by
  let s := DriverDimensions.state w 0 0 0
  have h1 := push_executes g (19:Fin 24) true s
  obtain ⟨c,hc,hcb⟩ := CNFCloneEmitter.WordEquality.program_executes g (stateBits w.source) (stateBits w.target)
  have h2 : (rename CNFCloneEmitter.WordEquality.program comparison).Executes g
      (Function.update s 19 [true]) (compared w) c := by
    apply rename_executes_to _ comparison g hc
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi
      have h16 : i≠16 := fun h => hi 0 h.symm
      have h17 : i≠17 := fun h => hi 1 h.symm
      have h19 : i≠19 := fun h => hi 2 h.symm
      simp only [compared,Function.update_of_ne h16,Function.update_of_ne h17,Function.update_of_ne h19]
      rfl
  refine ⟨c+3,?_,?_⟩
  · convert seq_executes _ _ g h1 h2 using 1 <;> omega
  · simp only [stateBits_length] at hcb;omega

lemma code_executes (g : BitString → ℕ) (s : Store 23) (b : Bool) :
    ∃c,code.Executes g (Function.update s 19 [b]) (Function.update s 19 (signedBits (if b then 1 else 0))) c ∧ c≤6 := by
  have he : Function.update (Function.update s (19:Fin 24) [b]) 19 []=Function.update s 19 [] := Function.update_idem ..
  cases b
  · refine ⟨3,?_,by omega⟩
    apply branchPop_false (19:Fin 24) _ _ _ g (rest:=[]) rfl
    rw [he]
    simpa [signedBits] using push_executes g (19:Fin 24) false (Function.update s 19 [])
  · refine ⟨6,?_,by omega⟩
    apply branchPop_true (19:Fin 24) _ _ _ g (rest:=[]) rfl
    rw [he]
    have h1 := push_executes g (19:Fin 24) true (Function.update s 19 [])
    have h2 := push_executes g (19:Fin 24) false
      (Function.update (Function.update s 19 []) 19 (true::Function.update s 19 [] 19))
    simpa [signedBits] using seq_executes _ _ g h1 h2

theorem evaluate_executes (g : BitString → ℕ) (w : WordInstance) :
    ∃s c,evaluate.Executes g (DriverDimensions.state w 0 0 0) s c ∧ s 19=signedBits (answer w) ∧
      c≤40*w.particles+24 := by
  obtain ⟨c,hc,hcb⟩ := compare_executes g w
  obtain ⟨d,hd,hdb⟩ := code_executes g
    (Function.update (Function.update (DriverDimensions.state w 0 0 0) 16 []) 17 [])
    (decide (stateBits w.source=stateBits w.target))
  refine ⟨_,_,seq_executes _ _ g hc hd,?_,by omega⟩
  simp only [Function.update_self]
  congr 1
  simp only [bits_equal,decide_eq_true_eq,answer]

theorem afterParse_executes (g : BitString → ℕ) (w : WordInstance) (hw : w.word=[]) :
    ∃c,afterParse.Executes g (DriverDimensions.state w 0 0 0)
      (Function.update (fun _ => []) 0 (signedBits (answer w))) c ∧ c≤2000*((wordBits w).length+1) := by
  have hin := wordBits_length_lower w
  have hb : ∀i,(DriverDimensions.state w 0 0 0 i).length≤(wordBits w).length := by
    intro i
    simp only [DriverDimensions.state]
    split_ifs <;> simp [hw,encodeBitList] <;> omega
  obtain ⟨s,c,hc,ho,hcb⟩ := evaluate_executes g w
  obtain ⟨d,hd,hdb⟩ := cleanResult_executes g (19:Fin 24) 20 (by decide) (by decide) (by decide)
    s ((wordBits w).length+c) (hc.stack_bound hb)
  rw [ho] at hd
  exact ⟨_,seq_executes _ _ g hc hd,by omega⟩
lemma compare_queryFree : compare.QueryFree := seq_queryFree _ _ (push_queryFree _ _)
  (rename_queryFree _ _ CNFCloneEmitter.WordEquality.program_queryFree)
lemma code_queryFree : code.QueryFree := branchPop_queryFree _ _ _ _ (push_queryFree _ _) (push_queryFree _ _)
  (seq_queryFree _ _ (push_queryFree _ _) (push_queryFree _ _))
lemma afterParse_queryFree : afterParse.QueryFree := seq_queryFree _ _
  (seq_queryFree _ _ compare_queryFree code_queryFree) (cleanResult_queryFree _ _ _ _)
end HiddenCircuits.GraphReduction.Runtime.WordGraph.EmptyWord
