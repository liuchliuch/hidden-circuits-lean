import HiddenCircuits.Approximation.SamplerRuntime.EndpointParserTriple

/-! Fresh, literal empty-word recognizer with full input consumption. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.EndpointParser
open Complexity OracleBlock
noncomputable def emptyCheck {k : ℕ} (a b : Fin (k+1)) : OracleBlock k :=
  branchPop a (push b true) (seq (clear a) (push b false)) (seq (clear a) (push b false))
theorem emptyCheck_executes {k : ℕ} (a b : Fin (k+1)) (hab : a≠b) (g : BitString → ℕ)
    (s : Store k) (hb : s b=[]) :
    ∃c,(emptyCheck a b).Executes g s
      (Function.update (Function.update s a []) b [(s a).isEmpty]) c ∧ c≤(s a).length+6 := by
  cases hs : s a with
  | nil =>
    refine ⟨3,?_,by simp [hs]⟩
    have he : Function.update s a []=s := by
      funext i; by_cases hi : i=a <;> simp [Function.update_apply,hi,hs]
    simpa [emptyCheck,hs,he,hb] using branchPop_empty a (push b true)
      (seq (clear a) (push b false)) (seq (clear a) (push b false)) g hs (push_executes g b true s)
  | cons v vs =>
    let t := Function.update s a vs
    have hh := seq_executes _ _ g (clear_executes g a t)
      (push_executes g b false (Function.update t a []))
    have ht : t a=vs := Function.update_self _ _ _
    have hb' : Function.update t a [] b=[] := by simp [t,Function.update_of_ne hab.symm,hb]
    simp only [ht,hb',Function.update_idem] at hh
    refine ⟨vs.length+6,?_,by simp [hs]⟩
    cases v with
    | false =>
      have hz := branchPop_false a (push b true) (seq (clear a) (push b false))
        (seq (clear a) (push b false)) g hs hh
      simpa [emptyCheck,t,Function.update_idem,hs,Nat.add_assoc] using hz
    | true =>
      have hz := branchPop_true a (push b true) (seq (clear a) (push b false))
        (seq (clear a) (push b false)) g hs hh
      simpa [emptyCheck,t,Function.update_idem,hs,Nat.add_assoc] using hz
lemma emptyCheck_queryFree {k : ℕ} (a b : Fin (k+1)) : (emptyCheck a b).QueryFree :=
  branchPop_queryFree _ _ _ _ (push_queryFree _ _)
    (seq_queryFree _ _ (clear_queryFree _) (push_queryFree _ _))
    (seq_queryFree _ _ (clear_queryFree _) (push_queryFree _ _))
end HiddenCircuits.Approximation.SamplerRuntime.EndpointParser
