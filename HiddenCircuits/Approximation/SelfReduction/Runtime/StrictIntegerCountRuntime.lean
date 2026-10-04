import HiddenCircuits.Approximation.SelfReduction.Runtime.StrictIntegerCountPreprocess

/-! New proof: one actual finite107-stack program executes coordinate parsing,
graph compilation, random counting, and all intervening workspace cleanup. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.StrictIntegerCounting
open Complexity Complexity.OracleBlock GraphReduction Polynomial

noncomputable def evaluate (raw : BitString) : BitString := GraphCounting.evaluate (preprocess raw)
noncomputable def program : OracleBlock 106 := precompose (resize preprocessProgram (by decide)) GraphCounting.program
noncomputable def time : Polynomial ℕ := precomposeTime (k:=106) preprocessTime GraphCounting.time preprocessSize

theorem program_executes (g : BitString → ℕ) (raw : BitString) :
    ∃s c,program.Executes g (Function.update (fun _=>[]) 0 raw) s c ∧s 0=evaluate raw ∧c≤time.eval raw.length := by
  apply precompose_executes _ _ g preprocess evaluate preprocessTime GraphCounting.time preprocessSize
  · intro x
    obtain ⟨s,c,hc,ho,hb⟩:=preprocess_executes g x
    obtain ⟨t,ht,he⟩:=resize_executes preprocessProgram (show 39≤106 by decide) g x s c hc
    exact ⟨t,c,ht,he.trans ho,hb⟩
  · exact preprocess_size
  · intro x
    obtain ⟨c,hc,hb⟩:=GraphCounting.raw_program_executes g (preprocess x)
    exact ⟨_,c,hc,Function.update_self _ _ _,hb⟩
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (rename_queryFree _ _ preprocess_queryFree)
  (seq_queryFree _ _ (cleanup_queryFree _) GraphCounting.program_queryFree)
theorem evaluate_polyTime : PolyTime evaluate :=
  polyTime_of_block program program_queryFree time (program_executes (fun _=>0))

lemma evaluate_canonical (G : GraphInput) (R : StrictIntegerRepresentation G) (r k : ℕ) (tape : BitString) :
    evaluate (pairBits (estimateInput (strictIntegerBits G R) r k) tape)=
      GraphCounting.evaluate (pairBits (estimateInput G.encode r k) tape) := by
  rw [evaluate,preprocess_canonical,GraphReduction.Runtime.StrictInteger.bits_representation]
lemma evaluate_unpaired (raw : BitString) (h:unpairBits raw=none) : evaluate raw=encodeRatio 0 0 := by
  rw [evaluate,preprocess_unpaired raw h]
  exact GraphCounting.evaluate_reject [] rfl

theorem canonical_executes (g : BitString → ℕ) (G : GraphInput) (R : StrictIntegerRepresentation G)
    (r k : ℕ) (tape : BitString) :
    ∃s c,program.Executes g (Function.update (fun _=>[]) 0 (pairBits (estimateInput (strictIntegerBits G R) r k) tape)) s c ∧
      s 0=GraphCounting.evaluate (pairBits (estimateInput G.encode r k) tape) ∧
      c≤time.eval (pairBits (estimateInput (strictIntegerBits G R) r k) tape).length := by
  simpa only [evaluate_canonical] using program_executes g (pairBits (estimateInput (strictIntegerBits G R) r k) tape)
lemma evaluate_raw (xs : BitString) (r k : ℕ) (tape : BitString) :
    evaluate (pairBits (estimateInput xs r k) tape)=GraphCounting.evaluate
      (pairBits (estimateInput (GraphReduction.Runtime.StrictInteger.graphInput xs).encode r k) tape) := by
  rw [evaluate,preprocess_canonical,GraphReduction.Runtime.StrictInteger.bits_graph]

end HiddenCircuits.Approximation.SelfReduction.Runtime.StrictIntegerCounting
