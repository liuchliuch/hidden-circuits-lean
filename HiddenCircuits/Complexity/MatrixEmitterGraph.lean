import HiddenCircuits.Complexity.MatrixEmitterSerialization
import Mathlib.Data.List.OfFn

namespace HiddenCircuits.Complexity.MatrixEmitter
open OracleBlock
variable {k : ℕ}

 theorem ofFn_nat {α : Type*} (n : ℕ) (f : ℕ → α) :
    List.ofFn (fun i : Fin n => f i.val)=(List.range n).map f := by
  apply List.ext_getElem <;> simp

 theorem matrixBits_graph {n : ℕ} (G : MatrixGraph n) (edge : ℕ → ℕ → Bool)
    (he : ∀ i j : Fin n, edge i.val j.val=G.edge i j) : matrixBits n edge=G.bits := by
  unfold MatrixGraph.bits
  rw [List.ofFn_mul]
  have hp : (List.ofFn fun i : Fin n => List.ofFn fun j : Fin n =>
      G.edge (finProdFinEquiv.symm ⟨i.val*n+j.val,by nlinarith [i.isLt,j.isLt]⟩).1
        (finProdFinEquiv.symm ⟨i.val*n+j.val,by nlinarith [i.isLt,j.isLt]⟩).2)=
      (List.ofFn fun i : Fin n => List.ofFn fun j : Fin n => edge i.val j.val) := by
    congr 1
    funext i
    congr 1
    funext j
    have hh : (⟨i.val*n+j.val,by nlinarith [i.isLt,j.isLt]⟩ : Fin (n*n))=finProdFinEquiv (i,j) := by
      apply Fin.ext
      change i.val*n+j.val=j.val+n*i.val
      ring
    rw [hh,Equiv.symm_apply_apply]
    exact (he i j).symm
  rw [hp]
  simp_rw [ofFn_nat]
  rw [ofFn_nat n (fun i => (List.range n).map (edge i))]
  rfl

 theorem queryBits_graph {n : ℕ} (G : MatrixGraph n) (edge : ℕ → ℕ → Bool)
    (he : ∀ i j : Fin n, edge i.val j.val=G.edge i j) : queryBits n edge=GraphInput.encode ⟨n,G⟩ := by
  simp only [queryBits,GraphInput.encode,matrixBits_graph G edge he]

/-- The emitted bytes are exactly the original graph encoding, not merely an abstract matrix object. -/
theorem graph_executes {n : ℕ} (G : MatrixGraph n) (B : OracleBlock (k+7)) (edge : ℕ → ℕ → Bool)
    (he : ∀ i j : Fin n, edge i.val j.val=G.edge i j) (T : ℕ) (params : Store (k+7))
    (hB : ∀ g i j out inner outer, i<n → j<n →
      ∃ c, B.Executes g (store n i j [] out inner outer params)
        (store n i j [edge i j] out inner outer params) c ∧ c≤T)
    (g : BitString → ℕ) :
    ∃ c, (block B).Executes g (store n 0 0 [] [] [] [] params)
      (Function.update (store n 0 0 [] [] [] [] params) (port 7) (GraphInput.encode ⟨n,G⟩)) c ∧
      c≤n*n*(T+18)+40*n+30 := by
  simpa only [queryBits_graph G edge he] using block_executes B edge n T params hB g

end HiddenCircuits.Complexity.MatrixEmitter
