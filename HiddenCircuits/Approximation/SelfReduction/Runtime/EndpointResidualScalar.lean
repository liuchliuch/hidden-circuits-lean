import HiddenCircuits.Approximation.SamplerRuntime.ReadLess
import HiddenCircuits.Approximation.SamplerRuntime.EndpointFiberBoundaries
import HiddenCircuits.Complexity.GraphVerifier.DropClock

/-! Literal unary threshold-and-pop boundary deletion. The selected column is
runtime data; no theorem or correctness certificate is consumed by the code. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.EndpointResidual
open Complexity OracleBlock
open SamplerRuntime.LengthLess SamplerRuntime.EndpointFiber GraphVerifier.Runtime

abbrev unary (n : ℕ) : BitString := List.replicate n true
noncomputable def scalarChoice : OracleBlock 5 := branchPop 2 skip skip (popDrop 1)
noncomputable def scalar : OracleBlock 5 := seq readLessBlock scalarChoice

lemma scalarChoice_executes (g : BitString  →  ℕ) (j t : ℕ) :
    scalarChoice.Executes g (readLessStore (unary j) (unary t) [decide (j<t)] [] [] [])
      (readLessStore (unary j) (unary (dropBoundary j t)) [] [] [] []) 3 := by
  by_cases h : j<t
  · have ht : 0<t := by omega
    obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t≠0)
    have hp := popDrop_executes (1:Fin 6) g (readLessStore (unary j) (unary (r+1)) [] [] [] [])
    have hp' : (popDrop (1:Fin 6)).Executes g
        (Function.update (readLessStore (unary j) (unary (r+1)) [true] [] [] []) 2 [])
        (readLessStore (unary j) (unary r) [] [] [] []) 1 := by
      convert hp using 1
      · funext i;fin_cases i <;> rfl
      · funext i;fin_cases i <;> simp [readLessStore,unary,List.replicate_succ]
    simpa [dropBoundary,h] using branchPop_true (2:Fin 6) skip skip (popDrop 1) g rfl hp'
  · have hs : Function.update (readLessStore (unary j) (unary t) [false] [] [] []) (2:Fin 6) []=
        readLessStore (unary j) (unary t) [] [] [] [] := by funext i;fin_cases i <;> rfl
    simpa [dropBoundary,h] using branchPop_false (2:Fin 6) skip skip (popDrop 1) g
      (s:=readLessStore (unary j) (unary t) [false] [] [] []) rfl (by rw [hs];exact skip_executes _ _)

theorem scalar_executes (g : BitString  →  ℕ) (j t : ℕ) :
    ∃cost, scalar.Executes g (readLessStore (unary j) (unary t) [] [] [] [])
      (readLessStore (unary j) (unary (dropBoundary j t)) [] [] [] []) cost ∧ cost ≤ 13*(j+t)+28 := by
  obtain ⟨c,hc,hb⟩ := readLess_executes g (unary j) (unary t)
  simp only [List.length_replicate] at hc hb
  exact ⟨_,seq_executes _ _ g hc (scalarChoice_executes g j t),by omega⟩

lemma scalar_queryFree : scalar.QueryFree := seq_queryFree _ _ readLess_queryFree
  (branchPop_queryFree _ _ _ _ skip_queryFree skip_queryFree (popDrop_queryFree _))

noncomputable def scalarOn {k : ℕ} (φ : Fin 6 ↪ Fin (k+1)) : OracleBlock k := rename scalar φ

theorem scalarOn_executes {k : ℕ} (φ : Fin 6 ↪ Fin (k+1)) (g : BitString  →  ℕ)
    (s : Store k) (j t : ℕ) (hs : s∘φ=readLessStore (unary j) (unary t) [] [] [] []) :
    ∃cost, (scalarOn φ).Executes g s (Function.update s (φ 1) (unary (dropBoundary j t))) cost ∧
      cost ≤ 13*(j+t)+28 := by
  obtain ⟨c,hc,hb⟩ := scalar_executes g j t
  refine ⟨c,?_,hb⟩
  apply rename_executes_to scalar φ g hc hs
  · funext i
    have he := congrFun hs i
    fin_cases i <;> simp_all [Function.comp_def,Function.update_apply,φ.injective.eq_iff,readLessStore]
  · intro i hi
    exact Function.update_of_ne (hi 1).symm _ _
lemma scalarOn_queryFree {k : ℕ} (φ : Fin 6 ↪ Fin (k+1)) : (scalarOn φ).QueryFree :=
  rename_queryFree _ _ scalar_queryFree
end HiddenCircuits.Approximation.SelfReduction.Runtime.EndpointResidual
