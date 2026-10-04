import HiddenCircuits.Approximation.SamplerRuntime.EndpointParserTriple
import HiddenCircuits.Complexity.GraphVerifier.BitChecks
import HiddenCircuits.Complexity.GraphVerifier.ReadOnlyAtLeast
import HiddenCircuits.Complexity.GraphVerifier.RuntimeDecision

/-! Concrete read-only unary checks and
charged register replacement. Both helpers compile to finite query-free code. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.EndpointParser
open Complexity OracleBlock GraphVerifier GraphVerifier.Runtime

def unaryCheckMap : Fin 1 ↪ Fin 3 where
  toFun _ := 1
  inj' := by intro i j _; exact Subsingleton.elim i j
noncomputable def unaryRead : OracleBlock 2 :=
  seq (copyOn 0 1 2 (by decide) (by decide) (by decide))
    (rename (BitChecks.block true) unaryCheckMap)
def unaryReadStore (a b c : BitString) : Store 2 := ![a,b,c]
theorem unaryRead_executes (g : BitString → ℕ) (xs : BitString) :
    unaryRead.Executes g (unaryReadStore xs [] []) (unaryReadStore xs [xs.all id] [])
      (6*xs.length+6) := by
  have h₁ : (copyOn (0:Fin 3) 1 2 (by decide) (by decide) (by decide)).Executes g
      (unaryReadStore xs [] []) (unaryReadStore xs xs []) (5*xs.length+2) := by
    convert copyOn_executes g (0:Fin 3) 1 2 (by decide) (by decide) (by decide) (unaryReadStore xs [] []) rfl using 1
    funext i; fin_cases i <;> simp [unaryReadStore]
  have h₂ : (rename (BitChecks.block true) unaryCheckMap).Executes g
      (unaryReadStore xs xs []) (unaryReadStore xs [xs.all id] []) (xs.length+2) := by
    apply rename_executes_to (BitChecks.block true) unaryCheckMap g (BitChecks.block_executes g true xs)
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [unaryReadStore,unaryCheckMap]; rfl
    · intro i hi; fin_cases i <;> first | rfl | exact False.elim (hi 0 rfl)
  convert seq_executes _ _ g h₁ h₂ using 1 <;> omega
lemma unaryRead_queryFree : unaryRead.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (rename_queryFree _ _ (BitChecks.block_queryFree _))
noncomputable def unaryReadOn {k : ℕ} (φ : Fin 3 ↪ Fin (k+1)) : OracleBlock k := rename unaryRead φ
theorem unaryReadOn_executes {k : ℕ} (φ : Fin 3 ↪ Fin (k+1)) (g : BitString → ℕ)
    (s : Store k) (xs : BitString) (hs : s∘φ=unaryReadStore xs [] []) :
    (unaryReadOn φ).Executes g s (Function.update s (φ 1) [xs.all id]) (6*xs.length+6) := by
  apply rename_executes_to unaryRead φ g (unaryRead_executes g xs) hs
  · have he : (Function.update s (φ 1) [xs.all id])∘φ=Function.update (s∘φ) 1 [xs.all id] := by
      funext i; simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]; funext i; fin_cases i <;> rfl
  · intro i hi; exact Function.update_of_ne (hi 1).symm _ _
lemma unaryReadOn_queryFree {k : ℕ} (φ : Fin 3 ↪ Fin (k+1)) : (unaryReadOn φ).QueryFree :=
  rename_queryFree _ _ unaryRead_queryFree

noncomputable def replaceOn {k : ℕ} (a b t : Fin (k+1)) (hab : a≠b) (hat : a≠t) (hbt : b≠t) : OracleBlock k :=
  seq (clear b) (seq (copyOn a b t hab hat hbt) (clear a))
theorem replaceOn_executes {k : ℕ} (a b t : Fin (k+1)) (hab : a≠b) (hat : a≠t) (hbt : b≠t)
    (g : BitString → ℕ) (s : Store k) (ht : s t=[]) :
    (replaceOn a b t hab hat hbt).Executes g s
      (Function.update (Function.update s b (s a)) a []) (6*(s a).length+(s b).length+8) := by
  have hc := copyOn_executes g a b t hab hat hbt (Function.update s b [])
    (by simpa [Function.update_of_ne hbt.symm] using ht)
  simp only [Function.update_of_ne hab,Function.update_self,List.append_nil] at hc
  have hh := seq_executes _ _ g (clear_executes g b s)
    (seq_executes _ _ g hc (clear_executes g a (Function.update (Function.update s b []) b (s a))))
  simp only [Function.update_idem,Function.update_of_ne hab] at hh
  convert hh using 1 <;> omega
lemma replaceOn_queryFree {k : ℕ} (a b t : Fin (k+1)) (hab : a≠b) (hat : a≠t) (hbt : b≠t) :
    (replaceOn a b t hab hat hbt).QueryFree :=
  seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (clear_queryFree _))
end HiddenCircuits.Approximation.SamplerRuntime.EndpointParser
