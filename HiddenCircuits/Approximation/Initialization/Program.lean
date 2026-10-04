import HiddenCircuits.Approximation.Initialization.Startup
import HiddenCircuits.Approximation.Initialization.OuterLoop.Semantics
import HiddenCircuits.Approximation.Initialization.InitializerOutput

/-! Complete fixed-52-stack graph-only matching initializer.
Every tape is interpreted by the concrete bounded stage search and cleanup. -/
namespace HiddenCircuits.Approximation.Initialization.Program
open Complexity Complexity.OracleBlock SamplerRuntime
set_option maxHeartbeats 2000000

noncomputable def block : OracleBlock 51 :=
  seq Startup.program (seq OuterLoop.loop OuterLoop.Finish.program)
noncomputable def timeBound (N k T : ℕ) : ℕ :=
  1000*(N+k+1)^4+
  OuterLoop.loopBound (Search.Stage.timeBound N (2*N+k) (N*N*(2*N+k))) N+
  OuterLoop.Finish.timeBound N (2*N+k) (N*N*(2*N+k)) T+4

lemma startup_executes (g : BitString → ℕ) {N : ℕ} (G : MatrixGraph N) (k : ℕ) (source : BitString) :
    ∃ t,Startup.program.Executes g (OuterLoop.state N G.bits [] source k [] 0 0 [])
      (OuterLoop.state N G.bits (MaskEnumerationSemantics.mask (Finset.univ : Finset (Fin N))) source (2*N+k)
        (Output.witness (Equiv.refl (Fin N))) (N*N*(2*N+k)) N []) t ∧
      t≤1000*(N+k+1)^4 := by
  obtain ⟨t,ht,hb⟩ := Startup.program_executes g N G.bits source k
  refine ⟨t,?_,hb⟩
  convert ht using 1
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> simp [OuterLoop.state,Startup.target,Startup.work,MaskEnumerationSemantics.mask]

theorem block_executes (g : BitString → ℕ) {N : ℕ} (G : MatrixGraph N) (k : ℕ) (source : BitString) :
    ∃ t,block.Executes g (OuterLoop.state N G.bits [] source k [] 0 0 [])
      (OuterLoop.state N G.bits [] [] 0 (initializerOutput G k source) 0 0 []) t ∧
      t≤timeBound N k source.length := by
  obtain ⟨a,ha,hab⟩ := startup_executes g G k source
  obtain ⟨V,ρ,tail,b,hb,hr,hlen,hbb⟩ := OuterLoop.loop_executes g G (2*N+k) N
    Finset.univ source (Equiv.refl (Fin N))
  obtain ⟨c,hc,hcb⟩ := OuterLoop.Finish.program_executes g G V tail (2*N+k) ρ
    (N*N*(2*N+k)) source.length hlen
  have hout : OuterLoop.Finish.code (OuterLoop.result V ρ)=initializerOutput G k source := by
    rw [initializerOutput_eq,hr]
    rfl
  rw [hout] at hc
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb hc),?_⟩
  change b≤OuterLoop.loopBound (Search.Stage.timeBound N (2*N+k) (N*N*(2*N+k))) N at hbb
  unfold timeBound
  omega

lemma block_queryFree : block.QueryFree := seq_queryFree _ _ Startup.program_queryFree
  (seq_queryFree _ _ OuterLoop.loop_queryFree OuterLoop.Finish.program_queryFree)

noncomputable def on {k : ℕ} (φ : Fin 52 ↪ Fin (k+1)) : OracleBlock k := rename block φ

def frameUpdate {k : ℕ} (φ : Fin 52 ↪ Fin (k+1)) (s : Store k) (out : BitString) : Store k :=
  Function.update (Function.update (Function.update s (φ 3) []) (φ 4) []) (φ 5) out

/-- A framed call preserves the graph, vertex count and every off-bank port. -/
theorem on_executes {k N : ℕ} (φ : Fin 52 ↪ Fin (k+1)) (g : BitString → ℕ)
    (s : Store k) (G : MatrixGraph N) (precision : ℕ) (source : BitString)
    (hs : s∘φ=OuterLoop.state N G.bits [] source precision [] 0 0 []) :
    ∃ t,(on φ).Executes g s (frameUpdate φ s (initializerOutput G precision source)) t ∧
      t≤timeBound N precision source.length := by
  obtain ⟨t,ht,hb⟩ := block_executes g G precision source
  refine ⟨t,rename_executes_to block φ g ht hs ?_ ?_,hb⟩
  · have he : (frameUpdate φ s (initializerOutput G precision source))∘φ=
        Function.update (Function.update (Function.update (s∘φ) 3 []) 4 []) 5
          (initializerOutput G precision source) := by
      funext i
      simp [frameUpdate,Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i;fin_cases i <;> rfl
  · intro i hi
    simp only [frameUpdate]
    rw [Function.update_of_ne (hi 5).symm,Function.update_of_ne (hi 4).symm,
      Function.update_of_ne (hi 3).symm]

lemma on_queryFree {k : ℕ} (φ : Fin 52 ↪ Fin (k+1)) : (on φ).QueryFree :=
  rename_queryFree _ _ block_queryFree
end HiddenCircuits.Approximation.Initialization.Program
