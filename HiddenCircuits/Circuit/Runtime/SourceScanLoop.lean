import HiddenCircuits.Circuit.Runtime.SourceScanBody

/-! Actual nested graph scan, linked to the full restoring edge circuit and its
exact scalar exponent; the initial output stream and normalization are framed. -/
namespace HiddenCircuits.Circuit.Runtime.SourceScan
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock Polynomial

def gateStream {n : ℕ} (gs : List (ConstraintGate n)) : BitString := encodeBitList (gs.map gateBits)
lemma gateStream_append {n : ℕ} (gs hs : List (ConstraintGate n)) :
    gateStream (gs++hs)=gateStream gs++gateStream hs := by
  simp [gateStream,encodeBitList_eq_flatMap]

noncomputable def loop : OracleBlock 35 := GridRuntime.program body
noncomputable def loopTime : Polynomial ℕ := (X+1)^2*(4500*(X+1)^2+40)+20*X+30

def prefixFrame {k : ℕ} (G : MatrixGraph (k+1)) (out : BitString) (swaps i j : ℕ) : GridRuntime.Frame 27 :=
  frame {wires:=k+1,payload:=G.bits,output:=(gateStream (scanGates G i j)).reverse++out,swaps:=swaps+2*scanSwaps G i j}

theorem loop_executes (g : BitString → ℕ) {k : ℕ} (G : MatrixGraph (k+1)) (output : BitString) (swaps : ℕ) :
    ∃ c, loop.Executes g
      (GridRuntime.initialStore k k (frame {wires:=k+1,payload:=G.bits,output:=output,swaps:=swaps}))
      (GridRuntime.initialStore k k (frame {wires:=k+1,payload:=G.bits,output:=(gateStream (restoringEdges (sourceEdges G)).gates).reverse++output,swaps:=swaps+2*restoringSwapPairs (sourceEdges G)})) c ∧
      c≤loopTime.eval (k+1) := by
  have hbody : GridRuntime.BodySpec body g k k (4500*(k+2)^2) (prefixFrame G output swaps) := by
    intro i j hi hj inner outer
    let ii : Fin (k+1) := ⟨i,by omega⟩
    let jj : Fin (k+1) := ⟨j,by omega⟩
    obtain ⟨c,hc,hcb⟩ := body_executes g G ii jj inner outer
      ((gateStream (scanGates G i j)).reverse++output) (swaps+2*scanSwaps G i j)
    refine ⟨c,?_,hcb⟩
    have hgs := scanGates_succ G ii jj
    have hss := scanSwaps_succ G ii jj
    dsimp only [ii,jj] at hgs hss hc
    simpa only [prefixFrame,store,hgs,hss,gateStream_append,List.reverse_append,List.append_assoc,
      Nat.mul_add,Nat.add_assoc] using hc
  have hrow : ∀ i, i≤k → prefixFrame G output swaps i (k+1)=prefixFrame G output swaps (i+1) 0 := by
    intro i hi
    simp only [prefixFrame,scanGates_row,scanSwaps_row]
  obtain ⟨c,hc,hcb⟩ := GridRuntime.program_executes body g k k (4500*(k+2)^2) (prefixFrame G output swaps) hbody hrow
  refine ⟨c,?_,hcb.trans ?_⟩
  · simpa only [prefixFrame,scanGates_zero,scanSwaps_zero,scanGates_final,scanSwaps_final,
      gateStream,List.map_nil,encodeBitList,List.reverse_nil,List.nil_append,Nat.mul_zero,Nat.add_zero] using hc
  · simpa only [loopTime,eval_add,eval_mul,eval_pow,eval_X,eval_ofNat,eval_one,Nat.add_assoc] using
      GridRuntime.programCost_bound k k (4500*(k+2)^2) (k+1) (by omega) (by omega)

lemma loop_queryFree : loop.QueryFree := GridRuntime.program_queryFree body body_queryFree

end HiddenCircuits.Circuit.Runtime.SourceScan
