import HiddenCircuits.Circuit.Runtime.SpectralFoldCell
import HiddenCircuits.Circuit.Runtime.SpectralWeightsPure
import HiddenCircuits.Circuit.Runtime.SpectralTable

/-! Genuine traversal of the basis table, with a proved invariant for every
partial common-denominator numerator vector. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralFold
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic Polynomial
open SpectralWeights

noncomputable def loop : OracleBlock 24 := whilePop 22 skip body
noncomputable def scalarBound : Polynomial ℕ := SpectralTable.entryBound*(X+1)^2+2
noncomputable def vectorBitPolynomial : Polynomial ℕ := SpectralTable.entryBound*(X+1)^2+SpectralTable.entryBound+(X+1)^2+2
noncomputable def vectorStreamBound : Polynomial ℕ := (X+1)^2*(2*vectorBitPolynomial+2)
noncomputable def argumentBound : Polynomial ℕ := scalarBound+SpectralTable.vectorBound+vectorStreamBound
noncomputable def time : Polynomial ℕ := (X+1)^2*(bodyTime.comp argumentBound+2)+1

 theorem scale_length (g : ℕ) (z : ℤ) (hz : z.natAbs≤1) (i : SpectralIndex g) :
    (signedBits (scale g z i)).length≤scalarBound.eval g := by
  have h := signedBits_length_of_abs_bound (scale_envelope g z hz i)
  simpa only [scalarBound,SpectralTable.entryBound,SpectralWeights.denominatorExponent,spectralBasisBitBound,
    eval_add,eval_mul,eval_pow,eval_X,eval_one,eval_ofNat] using h

 theorem vector_length_bound (g : ℕ) (z : ℤ) (hz : z.natAbs≤1) (done : List (SpectralIndex g))
    (hd : done.length≤(g+1)^2) :
    (encodeBitList ((vector g z done).map signedBits)).length≤vectorStreamBound.eval g := by
  have h := vector_stream_bound g z hz done hd
  simpa only [vectorStreamBound,vectorBitPolynomial,SpectralTable.entryBound,vectorBitBound,termExponent,
    SpectralWeights.denominatorExponent,spectralBasisBitBound,eval_add,eval_mul,eval_pow,eval_X,eval_one,eval_ofNat] using h

 theorem coefficient_length_bound (g : ℕ) (i : SpectralIndex g) :
    (encodeBitList ((SpectralBasis.coefficientVector g i).map signedBits)).length≤SpectralTable.vectorBound.eval g := by
  have hb : ∀c∈SpectralBasis.coefficientVector g i,(signedBits c).length≤SpectralTable.entryBound.eval g := by
    intro c hc
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hc
    have hh := (spectralBasis_bits g i k.val).1
    simpa only [signedBits,List.length_cons,encodeNat_length,SpectralTable.entryBound,eval_add,eval_mul,eval_pow,eval_X,eval_one,eval_ofNat] using hh
  have he := encodedWords_length_le ((SpectralBasis.coefficientVector g i).map signedBits)
    (SpectralTable.entryBound.eval g) (by intro w hw;obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hw;exact hb c hc)
  simp only [List.length_map,SpectralBasis.coefficientVector_length] at he
  apply he.trans
  simp only [SpectralTable.vectorBound,eval_mul,eval_pow,eval_add,eval_X,eval_one,eval_ofNat]
  exact Nat.mul_le_mul_right _ (spectralIndex_card_bound g)

 theorem loop_execution (oracle : BitString → ℕ) (g : ℕ) (z : ℤ) (hz : z.natAbs≤1)
    (todo done : List (SpectralIndex g)) (hlen : todo.length+done.length≤(g+1)^2) :
    ∃ t, WhileExecution (22:Fin 25) skip body oracle
      (state (encodeBitList ((vector g z done).map signedBits))
        (encodeBitList (todo.map (fun i => signedBits (scale g z i))))
        (encodeBitList (todo.map (fun i => encodeBitList ((SpectralBasis.coefficientVector g i).map signedBits)))) [] [] [])
      (state (encodeBitList ((vector g z (done++todo)).map signedBits)) [] [] [] [] []) t ∧
      t≤todo.length*(bodyTime.eval (argumentBound.eval g)+2)+1 := by
  induction todo generalizing done with
  | nil =>
    refine ⟨1,?_,by simp⟩
    simpa [encodeBitList] using (WhileExecution.empty (stack:=(22:Fin 25)) (B:=skip) (C:=body) (g:=oracle)
      (state (encodeBitList ((vector g z done).map signedBits)) [] [] [] [] []) rfl)
  | cons i todo ih =>
    have hq := scale_length g z hz i
    have hx := coefficient_length_bound g i
    have ha := vector_length_bound g z hz done (by simp only [List.length_cons] at hlen;omega)
    have hq' : (signedBits (scale g z i)).length≤argumentBound.eval g := by
      simp only [argumentBound,eval_add];omega
    have hx' : (encodeBitList ((SpectralBasis.coefficientVector g i).map signedBits)).length≤argumentBound.eval g := by
      simp only [argumentBound,eval_add];omega
    have ha' : (encodeBitList ((vector g z done).map signedBits)).length≤argumentBound.eval g := by
      simp only [argumentBound,eval_add];omega
    obtain ⟨c,hc,hcb⟩ := body_executes oracle (scale g z i) (SpectralBasis.coefficientVector g i) (vector g z done)
      (by simp [SpectralBasis.coefficientVector_length])
      (encodeBitList (todo.map (fun i => signedBits (scale g z i))))
      (encodeBitList (todo.map (fun i => encodeBitList ((SpectralBasis.coefficientVector g i).map signedBits))))
      (argumentBound.eval g) hq' hx' ha'
    have hu : update (scale g z i) (SpectralBasis.coefficientVector g i) (vector g z done)=vector g z (done++[i]) :=
      (vector_append_zipWith g z done i).symm
    rw [hu] at hc
    obtain ⟨t,ht,htb⟩ := ih (done++[i]) (by simp only [List.length_cons,List.length_append,List.length_nil] at *;omega)
    have he : Function.update
        (state (encodeBitList ((vector g z done).map signedBits))
          (encodeBitList ((i::todo).map (fun i => signedBits (scale g z i))))
          (encodeBitList ((i::todo).map (fun i => encodeBitList ((SpectralBasis.coefficientVector g i).map signedBits)))) [] [] [])
        (22:Fin 25) (pairBits (signedBits (scale g z i)) (encodeBitList (todo.map (fun i => signedBits (scale g z i)))))=
        state (encodeBitList ((vector g z done).map signedBits))
          (pairBits (signedBits (scale g z i)) (encodeBitList (todo.map (fun i => signedBits (scale g z i)))))
          (true::pairBits (encodeBitList ((SpectralBasis.coefficientVector g i).map signedBits))
            (encodeBitList (todo.map (fun i => encodeBitList ((SpectralBasis.coefficientVector g i).map signedBits))))) [] [] [] := by
      funext j;fin_cases j <;> rfl
    have hh := WhileExecution.one (show
        state (encodeBitList ((vector g z done).map signedBits))
          (encodeBitList ((i::todo).map (fun i => signedBits (scale g z i))))
          (encodeBitList ((i::todo).map (fun i => encodeBitList ((SpectralBasis.coefficientVector g i).map signedBits)))) [] [] [] 22=
          true::pairBits (signedBits (scale g z i)) (encodeBitList (todo.map (fun i => signedBits (scale g z i)))) from rfl)
      (by rw [he];exact hc) ht
    refine ⟨1+c+1+t,?_,?_⟩
    · simpa only [List.append_assoc,List.singleton_append] using hh
    · simp only [List.length_cons];nlinarith

 theorem loop_executes (oracle : BitString → ℕ) (g : ℕ) (z : ℤ) (hz : z.natAbs≤1) :
    ∃ t, loop.Executes oracle
      (state (encodeBitList ((List.replicate (Fintype.card (SpectralIndex g)) (0:ℤ)).map signedBits))
        (encodeBitList ((spectralIndices g).map (fun i => signedBits (scale g z i))))
        (encodeBitList (SpectralTable.vectors g)) [] [] [])
      (state (encodeBitList ((vector g z (spectralIndices g)).map signedBits)) [] [] [] [] []) t ∧ t≤time.eval g := by
  have hn : (spectralIndices g).length≤(g+1)^2 := by rw [spectralIndices_length];exact spectralIndex_card_bound g
  obtain ⟨t,ht,hb⟩ := loop_execution oracle g z hz (spectralIndices g) [] (by simpa using hn)
  refine ⟨t,?_,?_⟩
  · simpa only [vector_nil,List.nil_append] using whilePop_executes _ _ _ oracle ht
  · apply hb.trans
    simp only [time,eval_add,eval_mul,eval_pow,eval_comp,eval_X,eval_one,eval_ofNat]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) 1

 theorem loop_queryFree : loop.QueryFree := whilePop_queryFree _ _ _ skip_queryFree body_queryFree
end HiddenCircuits.Circuit.Runtime.SpectralFold
