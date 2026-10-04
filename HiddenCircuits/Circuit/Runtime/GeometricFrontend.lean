import HiddenCircuits.Circuit.Runtime.GeometricNodes
import HiddenCircuits.Circuit.Runtime.GeometricWeights
import HiddenCircuits.Circuit.Runtime.SpectralNodeOmission

/-! Unary degree and node index produce the actual signed
geometric interpolation weight, with every temporary root/node stream erased. -/
namespace HiddenCircuits.Circuit.Runtime.GeometricFrontend
open HiddenCircuits.Complexity OracleBlock BinaryArithmetic Polynomial IntegerSpectralWeights LagrangeIntegerArrays

def roots (d : ℕ) (i : Fin (d+1)) : List ℤ := otherNodes (List.finRange (d+1)) geometricIntegerNode i
def store (d j : ℕ) (x xs num den : BitString) : Store 24 := fun i =>
  if i.val=0 then x else if i.val=1 then xs else if i.val=2 then num else if i.val=3 then den
  else if i.val=23 then List.replicate d true else if i.val=24 then List.replicate j true else []
def nodesEmbedding : Fin 6 ↪ Fin 25 where
  toFun i := (![23,4,5,6,1,7] : Fin 6→Fin 25) i
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
def omissionEmbedding : Fin 8 ↪ Fin 25 where
  toFun i := (![1,24,0,4,5,6,7,8] : Fin 8→Fin 25) i
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
def weightsEmbedding : Fin 23 ↪ Fin 25 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun q : Fin 25=>q.val) h)
noncomputable def program : OracleBlock 24 := seq (rename GeometricNodes.program nodesEmbedding)
  (seq (rename SpectralNodeOmission.program omissionEmbedding)
    (seq (GeometricWeights.on weightsEmbedding) (seq (clear 0) (clear 1))))
noncomputable def streamSize : Polynomial ℕ := (X+1)*(2*(X+2)+2)
noncomputable def inputSize : Polynomial ℕ := X+2+streamSize
noncomputable def time : Polynomial ℕ := GeometricNodes.time+100*(streamSize+X+1)^2+
  GeometricWeights.time.comp inputSize+inputSize+12

lemma roots_length_le (d : ℕ) (i : Fin (d+1)) : (roots d i).length≤ d+1 := by
  simp only [roots,otherNodes,List.length_map]
  exact (List.length_filter_le _ _).trans_eq List.length_finRange
lemma root_word_length (d : ℕ) (i : Fin (d+1)) (z : ℤ) (hz : z∈roots d i) : (signedBits z).length≤ d+2 := by
  obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hz
  have h:=GeometricNodes.node_length j.val
  change (signedBits (geometricIntegerNode j)).length=j.val+2 at h
  rw [h]
  omega
lemma roots_stream_bound (d : ℕ) (i : Fin (d+1)) : (encodeBitList ((roots d i).map signedBits)).length≤ streamSize.eval d := by
  have h:=encodedWords_length_le ((roots d i).map signedBits) (d+2) (by
    intro w hw;obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hw;exact root_word_length d i z hz)
  simp only [List.length_map] at h
  have hm:=Nat.mul_le_mul_right (2*(d+2)+2) (roots_length_le d i)
  simp only [streamSize,eval_mul,eval_add,eval_X,eval_ofNat,eval_one]
  exact h.trans hm
lemma weights_input_bound (d : ℕ) (i : Fin (d+1)) : GeometricWeights.inputLength (geometricIntegerNode i) (roots d i)≤ inputSize.eval d := by
  have hx:=GeometricNodes.node_length i.val
  have hr:=roots_stream_bound d i
  change (signedBits (geometricIntegerNode i)).length=i.val+2 at hx
  simp only [GeometricWeights.inputLength,SpectralDenominator.inputLength,inputSize,eval_add,eval_X,eval_ofNat]
  omega

lemma erase_nodes (d : ℕ) (i : Fin (d+1)) :
    (((GeometricNodes.nodes d).map signedBits).eraseIdx i.val)=(roots d i).map signedBits := by
  rw [GeometricNodes.nodes_geometric,List.eraseIdx_map,List.eraseIdx_map,
    ←(List.nodup_finRange (d+1)).erase_getElem i.val (by simpa using i.isLt),
    (List.nodup_finRange (d+1)).erase_eq_filter]
  unfold roots otherNodes
  congr 2
  apply List.filter_congr
  intro j hj
  apply Bool.eq_iff_iff.mpr
  simp

set_option maxHeartbeats 800000 in
theorem program_executes (g : BitString → ℕ) (d : ℕ) (i : Fin (d+1)) :
    ∃c,program.Executes g (store d i.val [] [] [] [])
      (store d i.val [] [] (signedBits (geometricZeroNumerator d i)) (signedBits (geometricBasisDenominator d i))) c ∧
      c≤ time.eval d := by
  let all := encodeBitList ((GeometricNodes.nodes d).map signedBits)
  let rs := encodeBitList ((roots d i).map signedBits)
  let x := signedBits (geometricIntegerNode i)
  obtain ⟨a,ha,hab⟩:=GeometricNodes.program_executes g d
  have h1 : (rename GeometricNodes.program nodesEmbedding).Executes g (store d i.val [] [] [] []) (store d i.val [] all [] []) a := by
    apply rename_executes_to _ nodesEmbedding g ha
    · funext j;fin_cases j <;> rfl
    · funext j;fin_cases j <;> rfl
    · intro j hj;fin_cases j <;> first | rfl | exact (hj 4 rfl).elim
  have hj : i.val<((GeometricNodes.nodes d).map signedBits).length := by simpa [GeometricNodes.nodes,GeometricNodes.nodesFrom] using i.isLt
  obtain ⟨b,hb,hbb⟩:=SpectralNodeOmission.program_executes g ((GeometricNodes.nodes d).map signedBits) i.val hj
  have hselected : ((GeometricNodes.nodes d).map signedBits)[i.val]=x := by
    simp [GeometricNodes.nodes_geometric,List.getElem_map,x]
  rw [erase_nodes,hselected] at hb
  have h2 : (rename SpectralNodeOmission.program omissionEmbedding).Executes g
      (store d i.val [] all [] []) (store d i.val x rs [] []) b := by
    apply rename_executes_to _ omissionEmbedding g hb
    · funext j;fin_cases j <;> rfl
    · funext j;fin_cases j <;> rfl
    · intro j hj;fin_cases j <;> first | rfl | exact (hj 0 rfl).elim | exact (hj 2 rfl).elim
  obtain ⟨c,hc,hcb⟩:=GeometricWeights.program_executes g (geometricIntegerNode i) (roots d i)
  have hnum : denominator 0 (roots d i)=geometricZeroNumerator d i := GeometricWeights.geometric_numerator d i
  have hden : denominator (geometricIntegerNode i) (roots d i)=geometricBasisDenominator d i := rfl
  rw [hnum,hden] at hc
  have h3 : (GeometricWeights.on weightsEmbedding).Executes g (store d i.val x rs [] [])
      (store d i.val x rs (signedBits (geometricZeroNumerator d i)) (signedBits (geometricBasisDenominator d i))) c := by
    apply rename_executes_to _ weightsEmbedding g hc
    · funext j;fin_cases j <;> rfl
    · funext j;fin_cases j <;> rfl
    · intro j hj;fin_cases j <;> first | rfl | exact (hj 2 rfl).elim | exact (hj 3 rfl).elim
  have h4 : (clear (0:Fin 25)).Executes g
      (store d i.val x rs (signedBits (geometricZeroNumerator d i)) (signedBits (geometricBasisDenominator d i)))
      (store d i.val [] rs (signedBits (geometricZeroNumerator d i)) (signedBits (geometricBasisDenominator d i))) (x.length+1) := by
    convert clear_executes g (0:Fin 25) (store d i.val x rs (signedBits (geometricZeroNumerator d i)) (signedBits (geometricBasisDenominator d i))) using 1
    funext j;fin_cases j <;> rfl
  have h5 : (clear (1:Fin 25)).Executes g
      (store d i.val [] rs (signedBits (geometricZeroNumerator d i)) (signedBits (geometricBasisDenominator d i)))
      (store d i.val [] [] (signedBits (geometricZeroNumerator d i)) (signedBits (geometricBasisDenominator d i))) (rs.length+1) := by
    convert clear_executes g (1:Fin 25) (store d i.val [] rs (signedBits (geometricZeroNumerator d i)) (signedBits (geometricBasisDenominator d i))) using 1
    funext j;fin_cases j <;> rfl
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 (seq_executes _ _ g h4 h5))),?_⟩
  have hall:=GeometricNodes.stream_bound d
  have hr:=weights_input_bound d i
  have hmono:=polynomial_nat_eval_mono GeometricWeights.time hr
  dsimp only at hmono
  have hpow:=Nat.pow_le_pow_left (show all.length+i.val+1≤ streamSize.eval d+d+1 by
    simp only [streamSize,eval_mul,eval_add,eval_X,eval_ofNat,eval_one]
    dsimp only [all]
    omega) 2
  change x.length+rs.length≤ inputSize.eval d at hr
  simp only [time,eval_add,eval_mul,eval_pow,eval_comp,eval_X,eval_ofNat,eval_one]
  dsimp only [all] at hpow
  omega

lemma output_denominator_ne_zero (d : ℕ) (i : Fin (d+1)) : geometricBasisDenominator d i≠0 := geometricBasisDenominator_ne_zero d i
lemma output_length_bound (d : ℕ) (i : Fin (d+1)) :
    (signedBits (geometricZeroNumerator d i)).length≤(d+1)^2+2 ∧ (signedBits (geometricBasisDenominator d i)).length≤(d+1)^2+2 := by
  simpa [signedBits,encodeNat_length] using geometricZeroWeights_bits d i

lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (rename_queryFree _ _ GeometricNodes.program_queryFree)
  (seq_queryFree _ _ (rename_queryFree _ _ SpectralNodeOmission.program_queryFree)
    (seq_queryFree _ _ (GeometricWeights.on_queryFree _) (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _))))
noncomputable def on {k : ℕ} (φ : Fin 25 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 25 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (d : ℕ) (i : Fin (d+1)) (hs : s∘φ=store d i.val [] [] [] []) :
    ∃c,(on φ).Executes g s (Function.update (Function.update s (φ 2) (signedBits (geometricZeroNumerator d i)))
      (φ 3) (signedBits (geometricBasisDenominator d i))) c ∧ c≤time.eval d := by
  obtain ⟨c,hc,hb⟩:=program_executes g d i
  refine ⟨c,?_,hb⟩
  apply rename_executes_to _ φ g hc hs
  · funext j
    have hj:=congrFun hs j
    change s (φ j)=_ at hj
    simp only [Function.comp_def,Function.update_apply,φ.injective.eq_iff,hj]
    fin_cases j <;> rfl
  · intro j hj;simp only [Function.update_of_ne (hj 2).symm,Function.update_of_ne (hj 3).symm]
lemma on_queryFree {k : ℕ} (φ : Fin 25 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ program_queryFree
end HiddenCircuits.Circuit.Runtime.GeometricFrontend
