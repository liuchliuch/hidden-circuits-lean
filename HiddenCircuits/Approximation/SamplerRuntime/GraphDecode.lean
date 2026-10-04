import HiddenCircuits.Complexity.GraphVerifier.FinalRuntime

/-! Fresh reconstruction: accepted graph words are canonical, and the actual
independent-set verifier with the all-zero witness tests graph validity alone. -/
namespace HiddenCircuits.Complexity.MatrixGraph
lemma bits_ofBits {n : ℕ} {xs : BitString} {G : MatrixGraph n} (h : ofBits n xs=some G) : G.bits=xs := by
  unfold ofBits at h
  split at h
  next hl =>
    dsimp only at h
    split at h
    next hs =>
      split at h
      next hd =>
        cases h
        apply List.ext_getElem
        · simpa only [bits_length] using hl.symm
        · intro i hi hj
          simp only [bits,List.getElem_ofFn]
          change xs.get ⟨(finProdFinEquiv (finProdFinEquiv.symm ⟨i,by simpa using hi⟩)).val,_⟩=xs[i]
          simp [Nat.mod_add_div]
      next hd => simp at h
    next hs => simp at h
  next hl => simp at h

end HiddenCircuits.Complexity.MatrixGraph
namespace HiddenCircuits.Complexity.GraphInput
lemma decode_some {xs : BitString} {G : GraphInput} (h : decode xs=some G) : G.encode=xs := by
  unfold decode at h
  cases hu : unpairBits xs with
  | none => simp [hu] at h
  | some p =>
    rcases p with ⟨header,payload⟩
    simp only [hu] at h
    split_ifs at h with hh
    cases hg : MatrixGraph.ofBits header.length payload with
    | none => simp [hg] at h
    | some graph =>
      simp only [hg,Option.map_some,Option.some.injEq] at h
      subst G
      simp only [encode,MatrixGraph.bits_ofBits hg,←hh]
      exact pairBits_of_unpair xs header payload hu
end HiddenCircuits.Complexity.GraphInput
namespace HiddenCircuits.Approximation.SamplerRuntime.GraphParser
open Complexity GraphVerifier GraphVerifier.Runtime

def validationInput (raw : BitString) : BitString := pairBits raw (List.replicate raw.length false)
lemma validationInput_length (raw : BitString) : (validationInput raw).length=3*raw.length+1 := by
  simp [validationInput];omega
lemma validation_correct (raw : BitString) : verifier (validationInput raw)=(GraphInput.decode raw).isSome := by
  cases hg : GraphInput.decode raw with
  | none => simp [validationInput,verifier,verifyPair,hg]
  | some G =>
    have hn := GraphInput.decode_vertices_bound hg
    simp [validationInput,verifier,verifyPair,hg,hn,PaddedIndependent,MatrixGraph.ValidIndependent,
      restrictCertificate,ZeroPadded]
lemma fields_of_decode {raw : BitString} {G : GraphInput} (h : GraphInput.decode raw=some G) :
    (parse raw).left=List.replicate G.1 true ∧ (parse raw).right=G.2.bits := by
  rw [←GraphInput.decode_some h]
  simp [GraphInput.encode,parse_pair]
end HiddenCircuits.Approximation.SamplerRuntime.GraphParser
