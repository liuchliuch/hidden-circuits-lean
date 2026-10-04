import HiddenCircuits.Approximation.SamplerRuntime.OuterFinal
import HiddenCircuits.Approximation.SamplerRuntime.EndpointParserProgram

/-! An actual finite machine parses every raw input, initializes its own matching,
executes fair-bit switches, and cleans all work stacks. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.MonotoneSampler
open Complexity Complexity.OracleBlock GraphReduction.MonotoneEndpointEncoding

 theorem parserSpec : Outer.ParserSpec EndpointParser.program EndpointParser.time where
  queryFree := EndpointParser.program_queryFree
  executes g raw := by
    obtain ⟨c,hc,hb⟩ := EndpointParser.program_executes g raw
    refine ⟨EndpointParser.output raw,c,?_,?_,hb⟩
    · have hi : Function.update (fun _ : Fin 36 => ([]:BitString)) 0 raw=EndpointParser.input raw := by
        funext i;fin_cases i <;> rfl
      rw [hi]
      exact hc
    · exact ⟨rfl,EndpointParser.output_flag raw,fun E he => EndpointParser.output_fields he,
        EndpointParser.output_clean raw⟩

noncomputable def program : OracleBlock 44 := Outer.cleanProgram EndpointParser.program
noncomputable def time : Polynomial ℕ := Outer.cleanTime EndpointParser.time

/-- Every binary input has a genuine charged execution and clean result. -/
theorem program_executes (g : BitString → ℕ) (raw : BitString) :
    ∃cost,program.Executes g (Function.update (fun _ : Fin 45 => ([]:BitString)) 0 raw)
      (Function.update (fun _ : Fin 45 => ([]:BitString)) 0 (Functional.evaluate raw)) cost ∧ cost≤time.eval raw.length :=
  Outer.cleanProgram_executes EndpointParser.program EndpointParser.time parserSpec g raw

lemma program_queryFree : program.QueryFree :=
  Outer.cleanProgram_queryFree EndpointParser.program EndpointParser.time parserSpec

/-- The clean canonical interface used by the actual counting sampler batch. -/
theorem canonical_executes (g : BitString → ℕ) (E : Input) (k : ℕ) (coins : BitString) :
    ∃cost,program.Executes g
      (Function.update (fun _ : Fin 45 => ([]:BitString)) 0 (pairBits (sampleInput (encode E) k) coins))
      (Function.update (fun _ : Fin 45 => ([]:BitString)) 0
        (Core.evaluate E.2 (sampleInput (encode E) k).length coins)) cost ∧
      cost≤time.eval (pairBits (sampleInput (encode E) k) coins).length := by
  simpa only [Functional.evaluate_canonical] using program_executes g (pairBits (sampleInput (encode E) k) coins)

theorem evaluate_polyTime : PolyTime Functional.evaluate := by
  apply polyTime_of_block program program_queryFree time
  intro raw
  obtain ⟨c,hc,hb⟩ := program_executes (fun _ => 0) raw
  exact ⟨_,c,hc,Function.update_self _ _ _,hb⟩
noncomputable def randomProgram : RandomBitProgram := Functional.randomProgram evaluate_polyTime

end HiddenCircuits.Approximation.SamplerRuntime.MonotoneSampler
