import HiddenCircuits.Complexity.CNFCloneEmitter.CallbackCorrectness
import HiddenCircuits.Complexity.CNFCloneEmitter.Size

namespace HiddenCircuits.Complexity.CNFCloneEmitter
open OracleBlock
variable {n m : ℕ}

/-- Complete public layout: canonical formula8 and unary activities9/10 are
preserved, result7 is written, and every other stack is empty at entry/exit. -/
def inputStore (input : BitString) (a b : ℕ) (output : BitString) : Store 29 := fun i =>
  if i.val=7 then output else if i.val=8 then input else if i.val=9 then List.replicate a true
  else if i.val=10 then List.replicate b true else []

def dimensionReady (F : CNF n m) (a b : ℕ) : Store 29 := fun i =>
  if i.val=11 then Callback.payload F else if i.val=12 then List.replicate n true
  else if i.val=13 then List.replicate m true else inputStore F.bits a b [] i

def prepared (F : CNF n m) (a b : ℕ) : Store 29 :=
  MatrixEmitter.store (Callback.order (n:=n) (m:=m) a b) 0 0 [] [] [] [] (Callback.params F a b)

def dimensionEmbedding : Fin 8 ↪ Fin 30 where
  toFun i := (![8,11,21,12,22,23,13,24] : Fin 8 → Fin 30) i
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
noncomputable def dimensions : OracleBlock 29 := rename dimensionsBlock dimensionEmbedding
noncomputable def prepare : OracleBlock 29 := seq dimensions Size.block
noncomputable def cleanup : OracleBlock 29 := seq (clear 0) (seq (clear 11) (seq (clear 12) (seq (clear 13) (clear 14))))

theorem dimensions_executes_wide (g : BitString → ℕ) (F : CNF n m) (a b : ℕ) :
    ∃ cost, dimensions.Executes g (inputStore F.bits a b []) (dimensionReady F a b) cost ∧ cost≤30*F.bits.length+30 := by
  obtain ⟨c,hc,hb⟩ := dimensions_cnf g F
  refine ⟨c,?_,hb⟩
  apply rename_executes_to _ dimensionEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 1 rfl).elim | exact (hi 3 rfl).elim | exact (hi 6 rfl).elim

theorem size_executes (g : BitString → ℕ) (F : CNF n m) (a b : ℕ) :
    Size.block.Executes g (dimensionReady F a b) (prepared F a b)
      (20*n*a+5*m*b+16*n+9*m+9*a+26) := by
  have h := Size.executes g n m a b (dimensionReady F a b)
  convert h using 1
  · funext i;fin_cases i <;> simp [Size.store,dimensionReady,inputStore]
  · funext i;fin_cases i <;> simp [prepared,Size.store,dimensionReady,inputStore,MatrixEmitter.store,MatrixEmitter.port,
      Callback.params,Callback.order,Nat.mul_comm,Nat.mul_left_comm]

theorem prepare_executes (g : BitString → ℕ) (F : CNF n m) (a b : ℕ) :
    ∃ cost, prepare.Executes g (inputStore F.bits a b []) (prepared F a b) cost ∧
      cost≤30*F.bits.length+32+100*(n+m+a+b+1)^2 := by
  obtain ⟨c,hc,hb⟩ := dimensions_executes_wide g F a b
  have hs := size_executes g F a b
  refine ⟨c+(20*n*a+5*m*b+16*n+9*m+9*a+26)+2,seq_executes _ _ g hc hs,?_⟩
  have hsB := Size.cost_bound n m a b
  omega

theorem cleanup_executes (g : BitString → ℕ) (F : CNF n m) (a b : ℕ) (output : BitString) :
    cleanup.Executes g (Function.update (prepared F a b) 7 output) (inputStore F.bits a b output)
      (Callback.order (n:=n) (m:=m) a b+(Callback.payload F).length+n+m+n*2*a+13) := by
  let s := Function.update (prepared F a b) 7 output
  have h0 := clear_executes g (0:Fin 30) s
  have h1 := clear_executes g (11:Fin 30) (Function.update s 0 [])
  have h2 := clear_executes g (12:Fin 30) (Function.update (Function.update s 0 []) 11 [])
  have h3 := clear_executes g (13:Fin 30) (Function.update (Function.update (Function.update s 0 []) 11 []) 12 [])
  have h4 := clear_executes g (14:Fin 30) (Function.update (Function.update (Function.update (Function.update s 0 []) 11 []) 12 []) 13 [])
  have h := seq_executes _ _ g h0 (seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)))
  convert h using 1
  · funext i;fin_cases i <;> simp [s,prepared,inputStore,MatrixEmitter.store,MatrixEmitter.port,Callback.params]
  · simp [s,prepared,inputStore,MatrixEmitter.store,MatrixEmitter.port,Callback.params];omega

lemma prepare_queryFree : prepare.QueryFree := seq_queryFree _ _ (rename_queryFree _ _ dimensions_queryFree) Size.queryFree
lemma cleanup_queryFree : cleanup.QueryFree := seq_queryFree _ _ (clear_queryFree _)
  (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _))))

end HiddenCircuits.Complexity.CNFCloneEmitter
