import HiddenCircuits.Approximation.Initialization.Program
import HiddenCircuits.Approximation.SamplerRuntime.GraphInitializerEnvelope
import HiddenCircuits.Approximation.SamplerRuntime.PartnerInitialized

/-! Fully instantiated graph-only matching initializer for the
78-stack sampler. The switch-chain tape is outside the initializer bank. -/
namespace HiddenCircuits.Approximation.Initialization.SamplerInterface
open Complexity Complexity.OracleBlock SamplerRuntime Polynomial
set_option maxHeartbeats 2000000

noncomputable def init : PartnerInitialized.Initializer :=
  fun {_} G k tape => RawExtraction.initialPartner G k tape

def ports : Fin 52 ↪ Fin 78 where
  toFun i := if i.val=0 then 3 else if i.val=1 then 0 else if i.val=2 then 30
    else if i.val=3 then 29 else if i.val=4 then 31 else if i.val=5 then 2
    else ⟨i.val+26,by omega⟩
  inj' := by decide +kernel

noncomputable def prepare : OracleBlock 77 := copyOn 28 31 32 (by decide) (by decide) (by decide)
noncomputable def program : OracleBlock 77 := seq prepare (Program.on ports)
noncomputable def time : Polynomial ℕ := GraphInitializerEnvelope.time+5*X+4

lemma initialCode_eq {n : ℕ} (G : MatrixGraph n) (k : ℕ) (tape : BitString) :
    PartnerInitialized.initialCode G (init G k tape)=initializerOutput G k tape := by
  rfl

lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (Program.on_queryFree _)

/-- No initializer, certificate or callback is supplied: this is the concrete
program and its closed polynomial bound, for every finite initialization tape. -/
theorem spec : PartnerInitialized.InitializerSpec (extra:=48) program time init := by
  constructor
  · exact program_queryFree
  · intro n g G N hn initTape chainTape htape
    let s := PartnerInitialized.stageStore (extra:=48)
      (PartnerRunner.state G.bits n N chainTape [] [] []) initTape
    let s' := Function.update s (31:Fin 78) (List.replicate N true)
    have hp : prepare.Executes g s s' (5*N+2) := by
      convert copyOn_executes g (28:Fin 78) 31 32 (by decide) (by decide) (by decide) s rfl using 1
      · funext i;fin_cases i <;> simp [s,s',PartnerInitialized.stageStore,PartnerRunner.state]
      · simp [s,PartnerInitialized.stageStore,PartnerRunner.state,PartnerRunner.unary]
    have hs : s'∘ports=OuterLoop.state n G.bits [] initTape N [] 0 0 [] := by
      funext i;fin_cases i <;> rfl
    obtain ⟨b,hb,hbb⟩ := Program.on_executes ports g s' G N initTape hs
    have he : Program.frameUpdate ports s' (initializerOutput G N initTape)=
        PartnerInitialized.stageStore (extra:=48)
          (PartnerRunner.state G.bits n N chainTape (PartnerInitialized.initialCode G (init G N initTape)) [] []) [] := by
      rw [initialCode_eq]
      funext i;fin_cases i <;> rfl
    rw [he] at hb
    refine ⟨_,seq_executes _ _ g hp hb,?_⟩
    have hbound := GraphInitializerEnvelope.naturalBound_le hn (le_refl N) htape
    change Program.timeBound n N initTape.length≤GraphInitializerEnvelope.time.eval N at hbound
    simp only [time,eval_add,eval_mul,eval_ofNat,eval_X]
    omega

/-- The independent switch tape and input-size cap are not in the core bank. -/
lemma chainTape_disjoint (i : Fin 52) : ports i≠(5:Fin 78) := by
  fin_cases i <;> decide
lemma cap_disjoint (i : Fin 52) : ports i≠(28:Fin 78) := by
  fin_cases i <;> decide
end HiddenCircuits.Approximation.Initialization.SamplerInterface
