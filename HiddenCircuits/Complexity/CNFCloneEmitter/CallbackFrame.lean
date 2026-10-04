import HiddenCircuits.Complexity.CNFCloneEmitter.VertexClassifier
import HiddenCircuits.Complexity.CNFCloneEmitter.Incidence
import HiddenCircuits.Complexity.MatrixEmitterGraph
import HiddenCircuits.Complexity.GraphVerifier.ReadOnlyLength

namespace HiddenCircuits.Complexity.CNFCloneEmitter.Callback
open OracleBlock
variable {n m : ℕ}

def order (a b : ℕ) : ℕ := n*2*a+m*b
def payload (F : CNF n m) : BitString := encodeBitList ((List.ofFn F.clause).map CNF.clauseBits)

def params (F : CNF n m) (a b : ℕ) : Store 29 := fun k =>
  if k.val=8 then F.bits else if k.val=9 then List.replicate a true else if k.val=10 then List.replicate b true
  else if k.val=11 then payload F else if k.val=12 then List.replicate n true else if k.val=13 then List.replicate m true
  else if k.val=14 then List.replicate (n*2*a) true else []

/-- Eight generic matrix ports, seven preserved formula/activity masters, six
vertex descriptor fields, and nine work registers. -/
def state (F : CNF n m) (a b i j : ℕ) (bit out inner outer rt rn rs ct cn cs : BitString) : Store 29 := fun k =>
  if k.val=0 then List.replicate (order (n:=n) (m:=m) a b) true else if k.val=1 then List.replicate i true
  else if k.val=2 then List.replicate j true else if k.val=3 then bit else if k.val=4 then out
  else if k.val=5 then inner else if k.val=6 then outer else if k.val=7 then []
  else if k.val=15 then rt else if k.val=16 then rn else if k.val=17 then rs else if k.val=18 then ct
  else if k.val=19 then cn else if k.val=20 then cs else params F a b k

lemma state_matrix (F : CNF n m) (a b i j : ℕ) (bit out inner outer : BitString) :
    state F a b i j bit out inner outer [] [] [] [] [] [] =
      MatrixEmitter.store (order (n:=n) (m:=m) a b) i j bit out inner outer (params F a b) := by
  funext k;fin_cases k <;> simp [state,params,MatrixEmitter.store,MatrixEmitter.port]

def rowEmbedding : Fin 13 ↪ Fin 30 where
  toFun i := if i.val=0 then 1 else if i.val=1 then 14 else if i.val=2 then 9 else if i.val=3 then 10
    else if i.val=4 then 15 else if i.val=5 then 16 else if i.val=6 then 17
    else if i.val=7 then 21 else if i.val=8 then 22 else if i.val=9 then 23 else if i.val=10 then 24 else if i.val=11 then 25 else 26
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

def columnEmbedding : Fin 13 ↪ Fin 30 where
  toFun i := if i.val=0 then 2 else if i.val=1 then 14 else if i.val=2 then 9 else if i.val=3 then 10
    else if i.val=4 then 18 else if i.val=5 then 19 else if i.val=6 then 20
    else if i.val=7 then 21 else if i.val=8 then 22 else if i.val=9 then 23 else if i.val=10 then 24 else if i.val=11 then 25 else 26
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
noncomputable def row : OracleBlock 29 := VertexRuntime.on rowEmbedding
noncomputable def column : OracleBlock 29 := VertexRuntime.on columnEmbedding

def descriptor (a b i : ℕ) : Descriptor := decodeVertex (n*2*a) a b i

lemma positive_a {a b x : ℕ} (hx : x<n*2*a) : 0<a := by
  by_contra ha
  have he : a=0 := by omega
  simp [he] at hx
lemma positive_b {a b x : ℕ} (hx : x<order (n:=n) (m:=m) a b) (hy : n*2*a≤x) : 0<b := by
  by_contra hb
  have he : b=0 := by omega
  simp [order,he] at hx
  omega

theorem row_executes (g : BitString → ℕ) (F : CNF n m) (a b i j : ℕ) (hi : i<order (n:=n) (m:=m) a b)
    (bit out inner outer : BitString) :
    ∃ cost, row.Executes g (state F a b i j bit out inner outer [] [] [] [] [] [])
      (state F a b i j bit out inner outer [VertexRuntime.tag (descriptor (n:=n) a b i)]
        (List.replicate (VertexRuntime.number (descriptor (n:=n) a b i)) true)
        [VertexRuntime.sign (descriptor (n:=n) a b i)] [] [] []) cost ∧
      cost≤200*(i+n*2*a+a+b+1)^2 := by
  have hs : (state F a b i j bit out inner outer [] [] [] [] [] []) ∘ rowEmbedding =
      VertexRuntime.store i (n*2*a) a b [] 0 [] 0 0 0 [] [] 0 := by
    funext k;fin_cases k <;> rfl
  obtain ⟨c,hc,hb⟩ := VertexRuntime.on_executes rowEmbedding g _ i (n*2*a) a b
    (fun h => positive_a (b:=b) h) (positive_b hi) hs
  refine ⟨c,?_,hb⟩
  convert hc using 1
  funext k;fin_cases k <;> simp [state,params,rowEmbedding,descriptor]

theorem column_executes (g : BitString → ℕ) (F : CNF n m) (a b i j : ℕ) (hj : j<order (n:=n) (m:=m) a b)
    (bit out inner outer rt rn rs : BitString) :
    ∃ cost, column.Executes g (state F a b i j bit out inner outer rt rn rs [] [] [])
      (state F a b i j bit out inner outer rt rn rs [VertexRuntime.tag (descriptor (n:=n) a b j)]
        (List.replicate (VertexRuntime.number (descriptor (n:=n) a b j)) true)
        [VertexRuntime.sign (descriptor (n:=n) a b j)]) cost ∧
      cost≤200*(j+n*2*a+a+b+1)^2 := by
  have hs : (state F a b i j bit out inner outer rt rn rs [] [] []) ∘ columnEmbedding =
      VertexRuntime.store j (n*2*a) a b [] 0 [] 0 0 0 [] [] 0 := by
    funext k;fin_cases k <;> rfl
  obtain ⟨c,hc,hb⟩ := VertexRuntime.on_executes columnEmbedding g _ j (n*2*a) a b
    (fun h => positive_a (b:=b) h) (positive_b hj) hs
  refine ⟨c,?_,hb⟩
  convert hc using 1
  funext k;fin_cases k <;> simp [state,params,columnEmbedding,descriptor]

lemma row_queryFree : row.QueryFree := VertexRuntime.on_queryFree _
lemma column_queryFree : column.QueryFree := VertexRuntime.on_queryFree _

lemma descriptor_correct (a b : ℕ) (i : Fin (order (n:=n) (m:=m) a b)) :
    descriptor (n:=n) a b i.val = baseDescriptor ((CNF.cloneVertexFinEquiv (n:=n) (m:=m) a b).symm i).1 := by
  have h := decodeVertex_correct ((CNF.cloneVertexFinEquiv (n:=n) (m:=m) a b).symm i)
  simpa [descriptor] using h

end HiddenCircuits.Complexity.CNFCloneEmitter.Callback
