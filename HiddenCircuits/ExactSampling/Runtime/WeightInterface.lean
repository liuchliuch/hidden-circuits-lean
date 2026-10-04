import HiddenCircuits.ExactSampling.Runtime.WeightProgram
import HiddenCircuits.ExactSampling.DHWeights

/-! Composable public interface for the physical DH residual-weight compiler. -/
namespace HiddenCircuits.ExactSampling.Runtime.WeightCompiler
open Complexity OracleBlock
open Approximation.SelfReduction.Runtime

/-- The runtime weight word is the canonical encoding of the sampler's weight.
This bridge has no hereditary promise; that promise is used only to interpret
this number as a perfect-matching fiber cardinality. -/
lemma weightWord_eq_weight {N : ℕ} (G : MatrixGraph (N+1)) (j : Fin (N+1)) :
    weightWord G j=Computability.encodeNat (DHWeights.weight G j) := by
  cases he : G.edge 0 j
  · simp only [weightWord,DHWeights.weight,he,Bool.false_eq_true,ite_false];rfl
  · simp only [weightWord,DHWeights.weight,he,ite_true,DHWeights.count,GraphResidual.output]
    simp [DH.BinaryRuntime.function,DH.Runtime.BinaryModel.function,Computability.decode_encodeNat]

lemma output_positive {N : ℕ} (G : MatrixGraph (N+1)) :
    output ⟨N+1,G⟩=encodeBitList (List.ofFn (fun j => Computability.encodeNat (DHWeights.weight G j))) := by
  apply congrArg encodeBitList
  apply congrArg List.ofFn
  funext j
  exact weightWord_eq_weight G j

lemma store_initial (raw : BitString) : store raw []=Function.update (fun _=>[]) 0 raw := by
  funext i;fin_cases i <;> simp [store,state]

lemma store_zero (raw out : BitString) : store raw out 0=raw := rfl
lemma store_one (raw out : BitString) : store raw out 1=out := rfl
lemma store_scratch (raw out : BitString) (i : Fin 60) (h0:i≠0) (h1:i≠1) :
    store raw out i=[] := by
  have hi0 : i.val≠0 := by intro h;apply h0;exact Fin.ext h
  have hi1 : i.val≠1 := by intro h;apply h1;exact Fin.ext h
  simp [store,state,hi0,hi1]

/-- A fixed 60-stack finite query-free compiler, with exact byte-level endpoints. -/
theorem canonical_executes (g : BitString→ℕ) (G : GraphInput) :
    ∃t,program.Executes g (Function.update (fun _=>[]) 0 G.encode)
      (store G.encode (output G)) t ∧t≤timePolynomial.eval G.encode.length := by
  simpa only [←store_initial] using program_inputLengthBound g G

/-- Physical output storage is bounded by the actual execution clock. -/
lemma output_length (G : GraphInput) :
    (output G).length≤G.encode.length+timePolynomial.eval G.encode.length := by
  obtain ⟨t,ht,hb⟩ := canonical_executes (fun _=>0) G
  have hi : ∀q : Fin 60,(Function.update (fun _=>[]) 0 G.encode q).length≤G.encode.length := by
    intro q
    by_cases h:q=0
    · subst q;exact Nat.le_refl _
    · rw [Function.update_of_ne h];exact Nat.zero_le _
  have hs := ht.stack_bound hi (1:Fin 60)
  change (output G).length≤G.encode.length+t at hs
  omega

noncomputable def programOn {k : ℕ} (φ : Fin 60 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem programOn_executes {k : ℕ} (φ : Fin 60 ↪ Fin (k+1)) (g : BitString→ℕ)
    (s : Store k) (G : GraphInput) (hs:s∘φ=store G.encode []) :
    ∃t,(programOn φ).Executes g s (Function.update s (φ 1) (output G)) t ∧
      t≤timePolynomial.eval G.encode.length := by
  obtain ⟨t,ht,hb⟩ := program_inputLengthBound g G
  refine ⟨t,?_,hb⟩
  apply rename_executes_to program φ g ht hs
  · funext i
    simp only [Function.comp_apply,Function.update_apply,φ.injective.eq_iff]
    have hh := congrFun hs i
    simp only [Function.comp_apply] at hh
    rw [hh]
    fin_cases i <;> rfl
  · intro i hi
    exact Function.update_of_ne (hi 1).symm _ _

lemma programOn_queryFree {k : ℕ} (φ : Fin 60 ↪ Fin (k+1)) : (programOn φ).QueryFree :=
  rename_queryFree _ _ program_queryFree

theorem positive_executes (g : BitString→ℕ) {N : ℕ} (G : MatrixGraph (N+1)) :
    ∃t,program.Executes g (Function.update (fun _=>[]) 0 (GraphInput.encode ⟨N+1,G⟩))
      (store (GraphInput.encode ⟨N+1,G⟩)
        (encodeBitList (List.ofFn (fun j => Computability.encodeNat (DHWeights.weight G j))))) t ∧
      t≤timePolynomial.eval (GraphInput.encode ⟨N+1,G⟩).length := by
  simpa only [output_positive] using canonical_executes g ⟨N+1,G⟩

end HiddenCircuits.ExactSampling.Runtime.WeightCompiler
