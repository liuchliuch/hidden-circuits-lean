import HiddenCircuits.Circuit.Runtime.SourceCircuit
import HiddenCircuits.Circuit.Runtime.CircuitMetadata

/-! Emit the actual restoring source circuit, scalar
exponent, wire count, and two occurrence counts into five clean output ports. -/
namespace HiddenCircuits.Circuit.Runtime.SourceMetadata
open HiddenCircuits.Complexity OracleBlock Polynomial

def metadataEmbedding : Fin 9 ↪ Fin 36 where
  toFun i := (![0,2,3,4,5,6,7,8,9] : Fin 9 → Fin 36) i
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

def outputStore (circuit : BitString) (a n f z : ℕ) : Store 35 := fun i =>
  if i.val=0 then circuit else if i.val=1 then List.replicate a true else if i.val=2 then List.replicate n true
  else if i.val=3 then List.replicate f true else if i.val=4 then List.replicate z true else []
noncomputable def program : OracleBlock 35 := seq SourceCircuitEmitter.program (CircuitMetadata.on metadataEmbedding)
noncomputable def time : Polynomial ℕ := SourceCircuitEmitter.time+CircuitMetadata.time.comp SourceCircuitEmitter.circuitSize+2

set_option maxHeartbeats 600000 in
theorem program_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixGraph n) :
    ∃c, program.Executes g (Function.update (fun _=>[]) 0 (GraphInput.encode ⟨n,G⟩))
      (outputStore (circuitBits n (restoringIndependentProgram G).gates) (2*restoringSwapPairs (sourceEdges G))
        n (forbidOccurrences (restoringIndependentProgram G).gates) (signOccurrences (restoringIndependentProgram G).gates)) c ∧
      c≤time.eval (GraphInput.encode ⟨n,G⟩).length := by
  obtain ⟨a,ha,hab⟩ := SourceCircuitEmitter.program_executes g G
  obtain ⟨b,hb,hbb⟩ := CircuitMetadata.on_executes metadataEmbedding g
    (SourceCircuitEmitter.outputStore (circuitBits n (restoringIndependentProgram G).gates)
      (2*restoringSwapPairs (sourceEdges G))) (restoringIndependentProgram G).gates
    (by funext i;fin_cases i <;> rfl)
  have ht : Function.update (Function.update (Function.update
      (SourceCircuitEmitter.outputStore (circuitBits n (restoringIndependentProgram G).gates)
        (2*restoringSwapPairs (sourceEdges G))) (metadataEmbedding 1) (List.replicate n true))
        (metadataEmbedding 2) (List.replicate (forbidOccurrences (restoringIndependentProgram G).gates) true))
        (metadataEmbedding 3) (List.replicate (signOccurrences (restoringIndependentProgram G).gates) true)=
      outputStore (circuitBits n (restoringIndependentProgram G).gates) (2*restoringSwapPairs (sourceEdges G))
        n (forbidOccurrences (restoringIndependentProgram G).gates) (signOccurrences (restoringIndependentProgram G).gates) := by
    funext i;fin_cases i <;> rfl
  rw [ht] at hb
  refine ⟨_,seq_executes _ _ g ha hb,?_⟩
  have hn := GraphInput.vertices_le_length (⟨n,G⟩ : GraphInput)
  change n≤(GraphInput.encode ⟨n,G⟩).length at hn
  have hs := SourceCircuitEmitter.circuitSize_bound G
  have hm := polynomial_nat_eval_mono SourceCircuitEmitter.circuitSize hn
  dsimp only at hm
  have ht := polynomial_nat_eval_mono CircuitMetadata.time (hs.trans hm)
  dsimp only at ht
  simp only [time,eval_add,eval_comp,eval_ofNat]
  omega

lemma program_queryFree : program.QueryFree := seq_queryFree _ _ SourceCircuitEmitter.program_queryFree (CircuitMetadata.on_queryFree _)
noncomputable def on {k : ℕ} (φ : Fin 36 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 36 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    {n : ℕ} (G : MatrixGraph n)
    (hs : s∘φ=Function.update (fun _=>[]) 0 (GraphInput.encode ⟨n,G⟩)) :
    ∃c, (on φ).Executes g s
      (Function.update (Function.update (Function.update (Function.update (Function.update s (φ 0)
        (circuitBits n (restoringIndependentProgram G).gates)) (φ 1) (List.replicate (2*restoringSwapPairs (sourceEdges G)) true))
        (φ 2) (List.replicate n true)) (φ 3) (List.replicate (forbidOccurrences (restoringIndependentProgram G).gates) true))
        (φ 4) (List.replicate (signOccurrences (restoringIndependentProgram G).gates) true)) c ∧
      c≤time.eval (GraphInput.encode ⟨n,G⟩).length := by
  obtain ⟨c,hc,hb⟩ := program_executes g G
  refine ⟨c,?_,hb⟩
  apply rename_executes_to program φ g hc hs
  · funext i
    have hi:=congrFun hs i
    change s (φ i)=_ at hi
    simp only [Function.comp_def,Function.update_apply,φ.injective.eq_iff,hi]
    fin_cases i <;> rfl
  · intro i hi
    simp only [Function.update_of_ne (hi 0).symm,Function.update_of_ne (hi 1).symm,
      Function.update_of_ne (hi 2).symm,Function.update_of_ne (hi 3).symm,Function.update_of_ne (hi 4).symm]
lemma on_queryFree {k : ℕ} (φ : Fin 36 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ program_queryFree
end HiddenCircuits.Circuit.Runtime.SourceMetadata
