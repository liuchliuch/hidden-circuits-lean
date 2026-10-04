import HiddenCircuits.Circuit.Runtime.SourceScanTrue

/-! A real row-major adjacency lookup chooses whether to emit the corresponding
source circuit gates. The payload, loop metadata and all work frames survive. -/
namespace HiddenCircuits.Circuit.Runtime.SourceScan
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

lemma graph_bit {n : ℕ} (G : MatrixGraph n) (i j : Fin n) :
    G.bits[j.val+n*i.val]?.toList=[G.edge i j] := by
  change G.bits[(finProdFinEquiv (i,j)).val]?.toList=[G.edge i j]
  rw [List.getElem?_eq_getElem (by rw [MatrixGraph.bits_length];exact (finProdFinEquiv (i,j)).isLt)]
  simp only [MatrixGraph.bits,List.getElem_ofFn,Option.toList_some]
  change [G.edge (finProdFinEquiv.symm (finProdFinEquiv (i,j))).1 (finProdFinEquiv.symm (finProdFinEquiv (i,j))).2]=_
  rw [Equiv.symm_apply_apply]

noncomputable def readEdge : OracleBlock 35 := GraphVerifier.Runtime.matrixLookupOn lookupEmbedding
noncomputable def branchEdge : OracleBlock 35 := branchPop 15 skip skip trueEdge
noncomputable def body : OracleBlock 35 := seq readEdge branchEdge

lemma readEdge_executes (g : BitString → ℕ) {k : ℕ} (G : MatrixGraph (k+1)) (i j : Fin (k+1))
    (inner outer output : BitString) (swaps : ℕ) :
    readEdge.Executes g
      (store k i.val j.val inner outer {wires:=k+1,payload:=G.bits,output:=output,swaps:=swaps})
      (store k i.val j.val inner outer {wires:=k+1,payload:=G.bits,output:=output,swaps:=swaps,flag:=[G.edge i j]})
      (GraphVerifier.Runtime.matrixLookupCost (k+1) i.val j.val G.bits) := by
  have h := GraphVerifier.Runtime.matrixLookupOn_executes lookupEmbedding g
    (store k i.val j.val inner outer {wires:=k+1,payload:=G.bits,output:=output,swaps:=swaps})
    (k+1) i.val j.val G.bits (restrict_lookup _ _ _ _ _ _)
  simpa only [show lookupEmbedding 4=15 from rfl,graph_bit,update_flag] using h

lemma branchEdge_executes (g : BitString → ℕ) {k : ℕ} (G : MatrixGraph (k+1)) (i j : Fin (k+1))
    (inner outer output : BitString) (swaps : ℕ) :
    ∃ c, branchEdge.Executes g
      (store k i.val j.val inner outer {wires:=k+1,payload:=G.bits,output:=output,swaps:=swaps,flag:=[G.edge i j]})
      (store k i.val j.val inner outer {wires:=k+1,payload:=G.bits,output:=(encodeBitList ((edgeGates G i j).map gateBits)).reverse++output,swaps:=swaps+2*edgeSwapPairs G i j}) c ∧
      c≤4000*(k+2)^2+2 := by
  by_cases h : G.edge i j=true
  · obtain ⟨c,hc,hcb⟩ := trueEdge_executes g G i j h inner outer output swaps
    have hu : Function.update
        (store k i.val j.val inner outer {wires:=k+1,payload:=G.bits,output:=output,swaps:=swaps,flag:=[true]})
        (15 : Fin 36) []=store k i.val j.val inner outer {wires:=k+1,payload:=G.bits,output:=output,swaps:=swaps} := by
      rw [update_flag]
    have hb := branchPop_true (15 : Fin 36) skip skip trueEdge g
      (s := store k i.val j.val inner outer {wires:=k+1,payload:=G.bits,output:=output,swaps:=swaps,flag:=[true]})
      (rest := []) rfl (by rw [hu];exact hc)
    exact ⟨c+2,by simpa only [h] using hb,by omega⟩
  · have hf : G.edge i j=false := Bool.eq_false_iff.mpr h
    have hu : Function.update
        (store k i.val j.val inner outer {wires:=k+1,payload:=G.bits,output:=output,swaps:=swaps,flag:=[false]})
        (15 : Fin 36) []=store k i.val j.val inner outer {wires:=k+1,payload:=G.bits,output:=output,swaps:=swaps} := by
      rw [update_flag]
    have hb := branchPop_false (15 : Fin 36) skip skip trueEdge g
      (s := store k i.val j.val inner outer {wires:=k+1,payload:=G.bits,output:=output,swaps:=swaps,flag:=[false]})
      (rest := []) rfl (by rw [hu];exact skip_executes g _)
    exact ⟨3,by simpa [hf,edgeGates,edgeSwapPairs] using hb,by
      have hh : 1≤(k+2)^2 := Nat.one_le_pow _ _ (by omega)
      omega⟩

theorem body_executes (g : BitString → ℕ) {k : ℕ} (G : MatrixGraph (k+1)) (i j : Fin (k+1))
    (inner outer output : BitString) (swaps : ℕ) :
    ∃ c, body.Executes g
      (store k i.val j.val inner outer {wires:=k+1,payload:=G.bits,output:=output,swaps:=swaps})
      (store k i.val j.val inner outer {wires:=k+1,payload:=G.bits,output:=(encodeBitList ((edgeGates G i j).map gateBits)).reverse++output,swaps:=swaps+2*edgeSwapPairs G i j}) c ∧
      c≤4500*(k+2)^2 := by
  have hr := readEdge_executes g G i j inner outer output swaps
  obtain ⟨c,hc,hcb⟩ := branchEdge_executes g G i j inner outer output swaps
  refine ⟨_,seq_executes _ _ g hr hc,?_⟩
  have hb := GraphVerifier.Runtime.matrixLookupCost_in_range (k+1) i.val j.val G.bits i.isLt j.isLt
  nlinarith

lemma body_queryFree : body.QueryFree := seq_queryFree _ _ (GraphVerifier.Runtime.matrixLookupOn_queryFree _)
  (branchPop_queryFree _ _ _ _ skip_queryFree skip_queryFree trueEdge_queryFree)

end HiddenCircuits.Circuit.Runtime.SourceScan
