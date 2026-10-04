/- New wrapper, October2026, instantiated from the checked literal strict graph compiler. -/
import HiddenCircuits.Approximation.SamplerRuntime.StrictIntegerSamplerPreprocess

/-! A concrete query-free finite machine for literal strict integer-radius
sampling: compile the coordinates, preserve precision and coins, then sample. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.StrictIntegerSampler
open Complexity Complexity.OracleBlock GraphReduction Polynomial

noncomputable def evaluate (raw : BitString) : BitString := GraphFunctional.evaluate (preprocess raw)
noncomputable def program : OracleBlock 77 :=
  precompose (resize preprocessProgram (by decide)) GraphSampler.program
noncomputable def time : Polynomial ℕ :=
  precomposeTime (k:=77) preprocessTime GraphSampler.time preprocessSize

/-- Every parser and compiler step is included in the finite execution bound. -/
theorem program_executes (g : BitString → ℕ) (raw : BitString) :
    ∃s c,program.Executes g (Function.update (fun _=>[]) 0 raw) s c ∧
      s 0=evaluate raw ∧c≤time.eval raw.length := by
  apply precompose_executes _ _ g preprocess evaluate preprocessTime GraphSampler.time preprocessSize
  · intro x
    obtain ⟨s,c,hc,ho,hb⟩ := preprocess_executes g x
    obtain ⟨t,ht,he⟩ := resize_executes preprocessProgram (show 39≤77 by decide) g x s c hc
    exact ⟨t,c,ht,he.trans ho,hb⟩
  · exact preprocess_size
  · intro x
    obtain ⟨c,hc,hb⟩ := GraphSampler.program_executes g (preprocess x)
    exact ⟨_,c,hc,Function.update_self _ _ _,hb⟩

lemma program_queryFree : program.QueryFree :=
  seq_queryFree _ _ (rename_queryFree _ _ preprocess_queryFree)
    (seq_queryFree _ _ (cleanup_queryFree _) GraphSampler.program_queryFree)

theorem evaluate_polyTime : PolyTime evaluate :=
  polyTime_of_block program program_queryFree time (program_executes (fun _=>0))

lemma evaluate_canonical (G : GraphInput) (R : StrictIntegerRepresentation G) (k : ℕ) (tape : BitString) :
    evaluate (pairBits (sampleInput (strictIntegerBits G R) k) tape)=
      GraphFunctional.core G.2 ((sampleInput G.encode k).length+1) tape := by
  rw [evaluate,preprocess_canonical,Runtime.StrictInteger.bits_representation,GraphFunctional.evaluate_canonical]

/-- Malformed outer pairings have an explicit deterministic failure output. -/
lemma evaluate_unpaired (raw : BitString) (h : unpairBits raw=none) : evaluate raw=[] := by
  rw [evaluate,preprocess_unpaired raw h]
  rfl

/-- Canonical positive-radius representations need no precomputed graph or matching. -/
theorem canonical_executes (g : BitString → ℕ) (G : GraphInput)
    (R : StrictIntegerRepresentation G) (k : ℕ) (tape : BitString) :
    ∃s c,program.Executes g
      (Function.update (fun _=>[]) 0 (pairBits (sampleInput (strictIntegerBits G R) k) tape)) s c ∧
      s 0=GraphFunctional.core G.2 ((sampleInput G.encode k).length+1) tape ∧
      c≤time.eval (pairBits (sampleInput (strictIntegerBits G R) k) tape).length := by
  simpa only [evaluate_canonical] using program_executes g (pairBits (sampleInput (strictIntegerBits G R) k) tape)

lemma evaluate_raw (xs : BitString) (k : ℕ) (tape : BitString) :
    evaluate (pairBits (sampleInput xs k) tape)=GraphFunctional.evaluate
      (pairBits (sampleInput (GraphReduction.Runtime.StrictInteger.graphInput xs).encode k) tape) := by
  rw [evaluate,preprocess_canonical,GraphReduction.Runtime.StrictInteger.bits_graph]

end HiddenCircuits.Approximation.SamplerRuntime.StrictIntegerSampler
