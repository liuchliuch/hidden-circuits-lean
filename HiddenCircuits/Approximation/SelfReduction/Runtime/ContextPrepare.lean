import HiddenCircuits.Approximation.SelfReduction.Runtime.PairEmit
import HiddenCircuits.Approximation.Schemes

/-! Physically construct a fresh canonical sampler query from the current
residual graph bytes and preserved unary global precision. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

def contextStore (graph : BitString) (T : ℕ) (out work : BitString) : Store 4 := fun i =>
  if i.val=0 then graph else if i.val=1 then List.replicate T true
  else if i.val=2 then out else if i.val=3 then work else []

noncomputable def contextPrepare : OracleBlock 4 :=
  seq (copyOn 1 2 4 (by decide) (by decide) (by decide))
    (seq (copyOn 0 3 4 (by decide) (by decide) (by decide)) (pairEmit 3 2 4 (by decide) (by decide)))

 theorem contextPrepare_executes (g : BitString → ℕ) (graph : BitString) (T : ℕ) :
    contextPrepare.Executes g (contextStore graph T [] []) (contextStore graph T (sampleInput graph T) [])
      (5*T+13*graph.length+15) := by
  have h1 : (copyOn (1 : Fin 5) 2 4 (by decide) (by decide) (by decide)).Executes g
      (contextStore graph T [] []) (contextStore graph T (List.replicate T true) []) (5*T+2) := by
    convert copyOn_executes g (1 : Fin 5) 2 4 (by decide) (by decide) (by decide) (contextStore graph T [] []) rfl using 1
    · funext i; fin_cases i <;> simp [contextStore]
    · simp [contextStore]
  have h2 : (copyOn (0 : Fin 5) 3 4 (by decide) (by decide) (by decide)).Executes g
      (contextStore graph T (List.replicate T true) []) (contextStore graph T (List.replicate T true) graph) (5*graph.length+2) := by
    convert copyOn_executes g (0 : Fin 5) 3 4 (by decide) (by decide) (by decide) (contextStore graph T (List.replicate T true) []) rfl using 1
    funext i; fin_cases i <;> simp [contextStore]
  have h3 : (pairEmit (3 : Fin 5) 2 4 (by decide) (by decide)).Executes g
      (contextStore graph T (List.replicate T true) graph) (contextStore graph T (sampleInput graph T) []) (8*graph.length+7) := by
    convert pairEmit_executes g (3 : Fin 5) 2 4 (by decide) (by decide) (by decide)
      (contextStore graph T (List.replicate T true) graph) rfl using 1
    funext i; fin_cases i <;> simp [contextStore,sampleInput]
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 h3) using 1 <;> omega

 theorem contextPrepareOn_executes {k : ℕ} (φ : Fin 5 ↪ Fin (k+1)) (g : BitString → ℕ)
    (s : Store k) (graph : BitString) (T : ℕ) (hs : s∘φ=contextStore graph T [] []) :
    (rename contextPrepare φ).Executes g s (Function.update s (φ 2) (sampleInput graph T))
      (5*T+13*graph.length+15) := by
  apply rename_executes_to contextPrepare φ g (contextPrepare_executes g graph T) hs
  · funext i
    have hi := congrFun hs i
    fin_cases i <;> simp_all [Function.comp_def,Function.update_apply,φ.injective.eq_iff,contextStore]
  · intro j hj
    exact Function.update_of_ne (hj 2).symm _ _

 theorem pairEmit_queryFree {k : ℕ} (source output temp : Fin (k+1))
    (hst : source≠temp) (hto : temp≠output) : (pairEmit source output temp hst hto).QueryFree :=
  seq_queryFree _ _ (reverseOn_queryFree _ _ _) (seq_queryFree _ _ (push_queryFree _ _)
    (whilePop_queryFree _ _ _
      (seq_queryFree _ _ (push_queryFree _ _) (push_queryFree _ _))
      (seq_queryFree _ _ (push_queryFree _ _) (push_queryFree _ _))))

 theorem contextPrepare_queryFree : contextPrepare.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (pairEmit_queryFree _ _ _ _ _))

end HiddenCircuits.Approximation.SelfReduction.Runtime
