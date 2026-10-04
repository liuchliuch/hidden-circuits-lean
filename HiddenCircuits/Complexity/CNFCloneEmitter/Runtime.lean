import HiddenCircuits.Complexity.CNFCloneEmitter.Prepare
import HiddenCircuits.Complexity.CNFCloneEmitter.Bounds

/-! Complete actual finite emission of canonical independent-set clone queries
from arbitrary canonical CNF bytes and unary cloning activities. -/
namespace HiddenCircuits.Complexity.CNFCloneEmitter
open OracleBlock
variable {n m : ℕ}

noncomputable def matrix : OracleBlock 29 := MatrixEmitter.block Callback.program
noncomputable def program : OracleBlock 29 := seq prepare (seq matrix cleanup)

theorem matrix_executes (g : BitString → ℕ) (F : CNF n m) (a b : ℕ) :
    ∃ cost, matrix.Executes g (prepared F a b)
      (Function.update (prepared F a b) 7 (F.encodedCloneQuery a b)) cost ∧
      cost≤(Callback.order (n:=n) (m:=m) a b)*(Callback.order (n:=n) (m:=m) a b)*(Callback.time F a b+18)+
        40*(Callback.order (n:=n) (m:=m) a b)+30 := by
  exact MatrixEmitter.graph_executes (F.cloneQuery a b).2 Callback.program (Callback.edge F a b)
    (Callback.edge_fin F a b) (Callback.time F a b) (Callback.params F a b) (Callback.matrix_callback F a b) g

/-- The canonical formula and both activities are preserved; output7 is exactly
F.encodedCloneQuery, and every other stack is empty. Zero activities and the
empty graph are supported without additional premises. -/
theorem program_executes (g : BitString → ℕ) (F : CNF n m) (a b : ℕ) :
    ∃ cost, program.Executes g (inputStore F.bits a b [])
      (inputStore F.bits a b (F.encodedCloneQuery a b)) cost ∧
      cost≤timeBound.eval (F.bits.length+a+b) := by
  obtain ⟨cp,hp,hbp⟩ := prepare_executes g F a b
  obtain ⟨cm,hm,hbm⟩ := matrix_executes g F a b
  have hc := cleanup_executes g F a b (F.encodedCloneQuery a b)
  refine ⟨cp+(cm+(Callback.order (n:=n) (m:=m) a b+(Callback.payload F).length+n+m+n*2*a+13)+2)+2,
    seq_executes _ _ g hp (seq_executes _ _ g hm hc),?_⟩
  have hb := cost_bound F a b
  dsimp only at hb
  omega

lemma matrix_queryFree : matrix.QueryFree := MatrixEmitter.block_queryFree _ Callback.program_queryFree
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ prepare_queryFree
  (seq_queryFree _ _ matrix_queryFree cleanup_queryFree)

/-- Actual terminating OracleMachine run, with exact full-store result and
polynomial cost in the complete canonical input lengths. -/
theorem program_runs (g : BitString → ℕ) (F : CNF n m) (a b : ℕ) :
    ∃ cost, program.machine.Runs g (program.config program.start (inputStore F.bits a b []))
      (program.config program.exit (inputStore F.bits a b (F.encodedCloneQuery a b))) cost ∧
      cost≤timeBound.eval (F.bits.length+a+b) := by
  obtain ⟨c,hc,hb⟩ := program_executes g F a b
  refine ⟨c,?_,hb⟩
  apply (OracleMachine.runs_iff_steps_halt _).mpr
  exact ⟨hc,by simp [OracleMachine.step,OracleBlock.machine,OracleBlock.config,program.exit_halt]⟩

noncomputable def on {k : ℕ} (φ : Fin 30 ↪ Fin (k+1)) : OracleBlock k := rename program φ

/-- Arbitrary enclosing-machine frame. Only the designated output stack changes;
formula, unary activities and every external stack are preserved. -/
theorem on_executes {k : ℕ} (φ : Fin 30 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (F : CNF n m) (a b : ℕ) (hs : s ∘ φ=inputStore F.bits a b []) :
    ∃ cost, (on φ).Executes g s (Function.update s (φ 7) (F.encodedCloneQuery a b)) cost ∧
      cost≤timeBound.eval (F.bits.length+a+b) := by
  obtain ⟨c,hc,hb⟩ := program_executes g F a b
  refine ⟨c,?_,hb⟩
  apply rename_executes_to _ φ g hc hs
  · have he : (Function.update s (φ 7) (F.encodedCloneQuery a b)) ∘ φ=
        Function.update (s ∘ φ) 7 (F.encodedCloneQuery a b) := by
      funext i;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i;fin_cases i <;> rfl
  · intro i hi;exact Function.update_of_ne (hi 7).symm _ _
lemma on_queryFree {k : ℕ} (φ : Fin 30 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ program_queryFree

end HiddenCircuits.Complexity.CNFCloneEmitter
