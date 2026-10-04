import HiddenCircuits.Circuit.Runtime.SourceScanNormalize
import HiddenCircuits.Circuit.Runtime.RestoringEdgeEmitterOrientation

/-! Actual gate emission for a true adjacency bit, with both orientations and
normalization count handled by the same finite bit program. -/
namespace HiddenCircuits.Circuit.Runtime.SourceScan
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

noncomputable def trueEdge : OracleBlock 35 :=
  seq (EdgeEndpoints.on endpointsEmbedding) (seq (RestoringEdgeEmitter.on edgeEmbedding) normalize)

theorem trueEdge_executes (g : BitString → ℕ) {k : ℕ} (G : MatrixGraph (k+1)) (i j : Fin (k+1))
    (h : G.edge i j=true) (inner outer output : BitString) (swaps : ℕ) :
    ∃ c, trueEdge.Executes g
      (store k i.val j.val inner outer {wires:=k+1,payload:=G.bits,output:=output,swaps:=swaps})
      (store k i.val j.val inner outer {wires:=k+1,payload:=G.bits,output:=(encodeBitList ((edgeGates G i j).map gateBits)).reverse++output,swaps:=swaps+2*edgeSwapPairs G i j}) c ∧ c≤4000*(k+2)^2 := by
  let e : SourceEdge (k+1) := ⟨i,j,by intro hh;subst j;simpa [G.loopless] using h⟩
  let lo := RestoringEdgeEmitter.lower e
  let d := RestoringEdgeEmitter.distance e
  let v₀ : Values := {wires:=k+1,payload:=G.bits,output:=output,swaps:=swaps}
  let v₁ : Values := {v₀ with lo:=lo,distance:=d}
  let bytes := encodeBitList ((restoringEdgeProgram e).gates.map gateBits)
  let v₂ : Values := {v₁ with output:=bytes.reverse++output}
  obtain ⟨a,ha,hab⟩ := EdgeEndpoints.on_executes endpointsEmbedding g (store k i.val j.val inner outer v₀)
    i.val j.val (restrict_endpoints _ _ _ _ _ _)
  have h₀ : (EdgeEndpoints.on endpointsEmbedding).Executes g
      (store k i.val j.val inner outer v₀) (store k i.val j.val inner outer v₁) a := by
    simpa only [show endpointsEmbedding 2=13 from rfl,show endpointsEmbedding 3=14 from rfl,
      update_lo,update_distance] using ha
  obtain ⟨b,hb,hbb⟩ := RestoringEdgeEmitter.on_executes edgeEmbedding g
    (store k i.val j.val inner outer v₁) lo d (restrict_edge _ _ _ _ _ _)
  have h₁ : (RestoringEdgeEmitter.on edgeEmbedding).Executes g
      (store k i.val j.val inner outer v₁) (store k i.val j.val inner outer v₂) b := by
    have he : RestoringEdgeEmitter.bits lo d=bytes := RestoringEdgeEmitter.bits_eq_unordered_edge e
    rw [he] at hb
    simpa only [show edgeEmbedding 2=11 from rfl,update_output] using hb
  have h₂ := normalize_executes g k i.val j.val inner outer v₂
  have hdist : edgeSwapPairs G i j=d := by
    simp only [edgeSwapPairs,dif_pos h]
    rw [RestoringEdgeEmitter.route_normal_form,routeIndices_length]
  have hbytes : encodeBitList ((edgeGates G i j).map gateBits)=bytes := by
    simp only [edgeGates,dif_pos h]
    rfl
  have he := seq_executes _ _ g h₀ (seq_executes _ _ g h₁ h₂)
  refine ⟨a+(b+(11*d+lo+12)+2)+2,?_,?_⟩
  · simpa only [hdist,hbytes] using he
  · have hld : lo+d+1<k+1 := RestoringEdgeEmitter.ordered_bound e
    have hi := i.isLt
    have hj := j.isLt
    have hm := Nat.pow_le_pow_left (show lo+d+1≤k+2 by omega) 2
    simp only [RestoringEdgeEmitter.timeBound,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] at hbb
    nlinarith

lemma trueEdge_queryFree : trueEdge.QueryFree := seq_queryFree _ _ (EdgeEndpoints.on_queryFree _)
  (seq_queryFree _ _ (RestoringEdgeEmitter.on_queryFree _) normalize_queryFree)

end HiddenCircuits.Circuit.Runtime.SourceScan
