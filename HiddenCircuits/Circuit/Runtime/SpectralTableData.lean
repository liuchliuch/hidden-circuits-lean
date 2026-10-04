import HiddenCircuits.Circuit.Runtime.SpectralBasisCorrectness
import HiddenCircuits.Circuit.Runtime.SpectralFrontend

/-! Exact ordered basis-table bytes and their polynomial bounds. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralTable
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic Polynomial

 def defaultIndex (g : ℕ) : SpectralIndex g := ⟨⟨0,by omega⟩,⟨0,by simp⟩⟩
 def indexAt (g j : ℕ) : SpectralIndex g :=
  if h:j<(spectralIndices g).length then (spectralIndices g)[j] else defaultIndex g
 def denominatorWord (g j : ℕ) : BitString := signedBits (spectralBasisDenominator g (indexAt g j))
 def coefficientWord (g j : ℕ) : BitString :=
  encodeBitList ((SpectralBasis.coefficientVector g (indexAt g j)).map signedBits)
 def rootWord (g j : ℕ) : BitString :=
  encodeBitList ((SpectralBasis.roots g (indexAt g j)).map signedBits)
 def valueWord (g j : ℕ) : BitString := signedBits (spectralIntegerNode (indexAt g j))

 theorem range_map_indexAt {α : Type*} (g : ℕ) (f : SpectralIndex g → α) :
    (List.range (spectralIndices g).length).map (fun j => f (indexAt g j))=(spectralIndices g).map f := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    have h : j<(spectralIndices g).length := by simpa using hj
    simp [indexAt,h]

noncomputable def entryBound : Polynomial ℕ := (4*X+1)*(X+1)^2+2
noncomputable def vectorBound : Polynomial ℕ := (X+1)^2*(2*entryBound+2)
noncomputable def bodyTime : Polynomial ℕ := SpectralFrontend.time+SpectralBasis.spectralTime+
  6*vectorBound+6*entryBound+SpectralBasis.inputSize+29

 theorem denominatorWord_length (g j : ℕ) : (denominatorWord g j).length≤entryBound.eval g := by
  have hh := (spectralBasis_bits g (indexAt g j) 0).2
  simpa only [denominatorWord,signedBits,List.length_cons,encodeNat_length,entryBound,eval_add,eval_mul,eval_pow,eval_X,eval_one,eval_ofNat] using hh

 theorem coefficientWord_length (g j : ℕ) : (coefficientWord g j).length≤vectorBound.eval g := by
  have hb : ∀c∈SpectralBasis.coefficientVector g (indexAt g j),(signedBits c).length≤entryBound.eval g := by
    intro c hc
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hc
    have hh := (spectralBasis_bits g (indexAt g j) k.val).1
    simpa only [signedBits,List.length_cons,encodeNat_length,entryBound,eval_add,eval_mul,eval_pow,eval_X,eval_one,eval_ofNat] using hh
  have he := encodedWords_length_le ((SpectralBasis.coefficientVector g (indexAt g j)).map signedBits)
    (entryBound.eval g) (by intro w hw;obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hw;exact hb c hc)
  simp only [List.length_map,SpectralBasis.coefficientVector_length] at he
  apply he.trans
  simp only [vectorBound,eval_mul,eval_pow,eval_add,eval_X,eval_one,eval_ofNat]
  exact Nat.mul_le_mul_right _ (spectralIndex_card_bound g)

 theorem root_value_length (g j : ℕ) : (rootWord g j).length+(valueWord g j).length≤SpectralBasis.inputSize.eval g := by
  have h := SpectralBasis.spectral_input_length g (indexAt g j)
  unfold rootWord valueWord SpectralBasis.inputLength at *
  omega

noncomputable def emitOn {k : ℕ} (source out : Fin (k+1)) (hne : source≠out) : OracleBlock k :=
  rename wordEmit (pairEmbedding source out hne)

theorem emitOn_executes {k : ℕ} (g : BitString → ℕ) (source out : Fin (k+1)) (hne : source≠out) (s : Store k) :
    (emitOn source out hne).Executes g s
      (Function.update (Function.update s source []) out ((wordChunk (s source)).reverse++s out))
      (6*(s source).length+7) := by
  apply rename_executes_to wordEmit (pairEmbedding source out hne) g (wordEmit_executes g (s source) (s out))
  · funext i;fin_cases i <;> rfl
  · funext i
    fin_cases i
    · change (Function.update (Function.update s source []) out ((wordChunk (s source)).reverse++s out)) source=[]
      simp [hne]
    · change (Function.update (Function.update s source []) out ((wordChunk (s source)).reverse++s out)) out=((wordChunk (s source)).reverse++s out)
      simp
  · intro j hj
    have hs : j≠source := (hj 0).symm
    have ho : j≠out := (hj 1).symm
    simp [hs,ho]

theorem emitOn_queryFree {k : ℕ} (source out : Fin (k+1)) (hne : source≠out) : (emitOn source out hne).QueryFree :=
  rename_queryFree _ _ wordEmit_queryFree
end HiddenCircuits.Circuit.Runtime.SpectralTable
