import HiddenCircuits.Circuit.Runtime.SpectralNodesOuterBody

namespace HiddenCircuits.Circuit.Runtime.SpectralNodes
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic

def StageBound (x n B : ℕ) : Prop :=
  ∀a≤n,∀b≤n-a,(signedBits (((x*4^a*9^b:ℕ):ℤ))).length≤B

theorem StageBound.next {x n B : ℕ} (h : StageBound x (n+1) B) : StageBound (x*4) n B := by
  intro a ha b hb
  have hh := h (a+1) (by omega) b (by omega)
  have he : x*4*4^a*9^b=x*4^(a+1)*9^b := by ring
  rwa [he]

theorem StageBound.row {x n B : ℕ} (h : StageBound x n B) :
    ∀ y∈row (x:ℤ) n,(signedBits y).length≤B := by
  intro y hy
  rw [row_eq_range] at hy
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hy
  have hb' := List.mem_range.mp hb
  have hh := h 0 (by omega) b (by omega)
  simpa using hh

theorem StageBound.final {x n B : ℕ} (h : StageBound x n B) :
    (signedBits ((x:ℤ)*9^n)).length≤B := by
  have hh := h 0 (by omega) n (by omega)
  simpa using hh

noncomputable def outerLoop : OracleBlock 12 := whilePop 11 outerBody outerBody

theorem outer_execution (oracle : BitString → ℕ) (n x g B : ℕ) (out : BitString)
    (hx : 0<x) (hB : StageBound x n B) :
    ∃ t, WhileExecution (11:Fin 13) outerBody outerBody oracle (outerState x n g out)
      (outerState (x*4^n) 0 g ((encodeBitList ((triangle (x:ℤ) n).map signedBits)).reverse++out)) t ∧
      t≤n*((n+1)*(bodyTime.eval B+2)+6*B+5*n+32)+1 := by
  induction n generalizing x out with
  | zero =>
    refine ⟨1,?_,by omega⟩
    simpa [triangle,encodeBitList] using (WhileExecution.empty (stack:=(11:Fin 13)) (B:=outerBody) (C:=outerBody) (g:=oracle) (outerState x 0 g out) rfl)
  | succ n ih =>
    obtain ⟨c,hc,hcb⟩ := outerBody_executes oracle x n g out hx B hB.row hB.final
    have hs : Function.update (outerState x (n+1) g out) (11:Fin 13) (List.replicate n true)=outerState x n g out := by
      funext i;fin_cases i <;> simp [outerState]
    rw [←hs] at hc
    obtain ⟨d,hd,hdb⟩ := ih (x*4) ((encodeBitList ((row (x:ℤ) (n+1)).map signedBits)).reverse++out)
      (by omega) hB.next
    have hh := WhileExecution.one (stack:=(11:Fin 13))
      (show outerState x (n+1) g out 11=true::List.replicate n true from rfl) hc hd
    have he : x*4*4^n=x*4^(n+1) := by ring
    refine ⟨c+d+2,?_,?_⟩
    · convert hh using 1 <;>
      (try simp only [he,triangle,List.map_append,encodeBitList_append,List.reverse_append,List.append_assoc,Nat.cast_mul,Nat.cast_ofNat]) <;> omega
    · nlinarith [Nat.zero_le (bodyTime.eval B)]

theorem outerLoop_executes (oracle : BitString → ℕ) (n x g B : ℕ) (out : BitString)
    (hx : 0<x) (hB : StageBound x n B) :
    ∃ t, outerLoop.Executes oracle (outerState x n g out)
      (outerState (x*4^n) 0 g ((encodeBitList ((triangle (x:ℤ) n).map signedBits)).reverse++out)) t ∧
      t≤n*((n+1)*(bodyTime.eval B+2)+6*B+5*n+32)+1 := by
  obtain ⟨t,ht,hb⟩ := outer_execution oracle n x g B out hx hB
  exact ⟨t,whilePop_executes _ _ _ _ ht,hb⟩
theorem outerLoop_queryFree : outerLoop.QueryFree := whilePop_queryFree _ _ _ outerBody_queryFree outerBody_queryFree
end HiddenCircuits.Circuit.Runtime.SpectralNodes
