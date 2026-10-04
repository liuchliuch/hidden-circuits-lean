import HiddenCircuits.Approximation.Initialization.InducedEntry
import HiddenCircuits.Approximation.Initialization.MaskEnumerationFrame
import HiddenCircuits.Approximation.Initialization.WordMatrixEmitter

/-! Canonical graph encoding for the actual retained induced graph,
emitted by a fixed finite row-major program from its real mask enumeration. -/
namespace HiddenCircuits.Approximation.Initialization.InducedGraphEmitter
open Complexity Complexity.OracleBlock

def indexWords {N : ℕ} (U : Finset (Fin N)) : List BitString :=
  List.ofFn (fun i : Fin U.card => List.replicate (ResidualTest.vertex U i).val true)

def induced {N : ℕ} (G : MatrixGraph N) (U : Finset (Fin N)) : MatrixGraph U.card where
  edge i j := G.edge (ResidualTest.vertex U i) (ResidualTest.vertex U j)
  symm i j := G.symm _ _
  loopless i := G.loopless _

theorem induced_graph {N : ℕ} (G : MatrixGraph N) (U : Finset (Fin N)) :
    (induced G U).graph = ResidualTest.graph G.graph U := rfl

def edge {N : ℕ} (G : MatrixGraph N) (U : Finset (Fin N)) (i j : ℕ) : Bool :=
  if hi : i < U.card then if hj : j < U.card then (induced G U).edge ⟨i,hi⟩ ⟨j,hj⟩ else false else false

theorem indexWords_length_bound {N : ℕ} (U : Finset (Fin N)) :
    (encodeBitList (indexWords U)).length ≤ U.card*(2*N+2) := by
  have h := WordMatrixEmitter.encode_length_bound (indexWords U) N (by
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    simpa using (ResidualTest.vertex U i).isLt.le)
  simpa [indexWords] using h

def initial {N : ℕ} (G : MatrixGraph N) (U : Finset (Fin N)) : Store 16 :=
  MatrixEmitter.store U.card 0 0 [] [] [] []
    (InducedEntry.params N G.bits (encodeBitList (indexWords U)))

noncomputable def program : OracleBlock 16 := MatrixEmitter.block InducedEntry.program

def timeBound (N n L : ℕ) : ℕ := n*n*(500*(N+n+L+1)^2+18)+40*n+30

theorem program_executes (g : BitString → ℕ) {N : ℕ} (G : MatrixGraph N) (U : Finset (Fin N)) :
    ∃ t, program.Executes g (initial G U)
      (Function.update (initial G U) 7 (GraphInput.encode ⟨U.card,induced G U⟩)) t ∧
      t ≤ timeBound N U.card (encodeBitList (indexWords U)).length := by
  apply MatrixEmitter.graph_executes (induced G U) InducedEntry.program (edge G U)
    (by intro i j; simp [edge,i.isLt,j.isLt])
  intro g i j out inner outer hi hj
  obtain ⟨t,ht,hb⟩ := InducedEntry.program_executes g G (indexWords U) U.card i j out inner outer
    (ResidualTest.vertex U ⟨i,hi⟩) (ResidualTest.vertex U ⟨j,hj⟩) hi hj
    (by simp [indexWords,hi]) (by simp [indexWords,hj])
  refine ⟨t,?_,hb⟩
  convert ht using 1 <;> funext r <;> fin_cases r <;>
    simp [InducedEntry.state,InducedEntry.params,MatrixEmitter.store,MatrixEmitter.port,edge,hi,hj,induced]

theorem program_queryFree : program.QueryFree :=
  MatrixEmitter.block_queryFree _ InducedEntry.program_queryFree

noncomputable def on {k : ℕ} (φ : Fin 17 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k N : ℕ} (φ : Fin 17 ↪ Fin (k+1)) (g : BitString → ℕ)
    (s : Store k) (G : MatrixGraph N) (U : Finset (Fin N)) (hs : s ∘ φ = initial G U) :
    ∃ t, (on φ).Executes g s
      (Function.update s (φ 7) (GraphInput.encode ⟨U.card,induced G U⟩)) t ∧
      t ≤ timeBound N U.card (encodeBitList (indexWords U)).length := by
  obtain ⟨t,ht,hb⟩ := program_executes g G U
  refine ⟨t,?_,hb⟩
  apply rename_executes_to program φ g ht hs
  · funext r
    simp only [Function.comp_apply,Function.update_apply,φ.injective.eq_iff]
    have hh := congrFun hs r
    simp only [Function.comp_apply] at hh
    rw [hh]
  · intro r hr
    exact Function.update_of_ne (hr 7).symm _ _

theorem on_queryFree {k : ℕ} (φ : Fin 17 ↪ Fin (k+1)) : (on φ).QueryFree :=
  rename_queryFree _ _ program_queryFree

end HiddenCircuits.Approximation.Initialization.InducedGraphEmitter
