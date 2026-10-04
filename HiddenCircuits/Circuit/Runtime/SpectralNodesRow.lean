import HiddenCircuits.Circuit.Runtime.SpectralNodesCell
import HiddenCircuits.Complexity.PolynomialBounds

namespace HiddenCircuits.Circuit.Runtime.SpectralNodes
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic
noncomputable def rowProgram : OracleBlock 9 := whilePop 6 body body

theorem row_execution (g : BitString → ℕ) (n : ℕ) (x : ℤ) (out : BitString) (B : ℕ)
    (hB : ∀ y∈row x n,(signedBits y).length≤B) :
    ∃ t, WhileExecution (6:Fin 10) body body g (state x (List.replicate n true) out)
      (state (x*9^n) [] ((encodeBitList ((row x n).map signedBits)).reverse++out)) t ∧
      t≤n*(bodyTime.eval B+2)+1 := by
  induction n generalizing x out with
  | zero =>
    refine ⟨1,?_,by omega⟩
    simpa [row,encodeBitList] using (WhileExecution.empty (stack:=(6:Fin 10)) (B:=body) (C:=body) (g:=g) (state x [] out) rfl)
  | succ n ih =>
    have hx : (signedBits x).length≤B := hB x (by simp [row])
    have hr : ∀y∈row (x*9) n,(signedBits y).length≤B := by
      intro y hy;exact hB y (by simp [row,hy])
    obtain ⟨c,hc,hcb⟩ := body_executes g x (List.replicate n true) out
    have hs : Function.update (state x (List.replicate (n+1) true) out) (6:Fin 10) (List.replicate n true)=
        state x (List.replicate n true) out := by
      funext i;fin_cases i <;> simp [state]
    rw [←hs] at hc
    obtain ⟨d,hd,hdb⟩ := ih (x*9) ((wordChunk (signedBits x)).reverse++out) hr
    have hh := WhileExecution.one (stack:=(6:Fin 10)) (show state x (List.replicate (n+1) true) out 6=true::List.replicate n true from rfl) hc hd
    have he : x*9*9^n=x*9^(n+1) := by ring
    refine ⟨c+d+2,?_,?_⟩
    · convert hh using 1 <;>
      (try simp only [he,row,List.map_cons,encodeBitList_eq_chunks,List.flatMap_cons,List.flatMap_nil,
        List.reverse_append,List.append_assoc]) <;> omega
    · have hm := polynomial_nat_eval_mono bodyTime hx
      nlinarith

theorem rowProgram_executes (g : BitString → ℕ) (n : ℕ) (x : ℤ) (out : BitString) (B : ℕ)
    (hB : ∀ y∈row x n,(signedBits y).length≤B) :
    ∃ t, rowProgram.Executes g (state x (List.replicate n true) out)
      (state (x*9^n) [] ((encodeBitList ((row x n).map signedBits)).reverse++out)) t ∧
      t≤n*(bodyTime.eval B+2)+1 := by
  obtain ⟨t,ht,hb⟩ := row_execution g n x out B hB
  exact ⟨t,whilePop_executes _ _ _ _ ht,hb⟩

theorem rowProgram_queryFree : rowProgram.QueryFree := whilePop_queryFree _ _ _ body_queryFree body_queryFree
end HiddenCircuits.Circuit.Runtime.SpectralNodes
