import HiddenCircuits.Approximation.SamplerRuntime.Switch

/-! Bit-length bounds for the literal array reads, updates and endpoint checks. -/
namespace HiddenCircuits.Approximation.SamplerRuntime
open Complexity DH.Runtime

lemma word_length_le_encoded (ws : List BitString) (i : ℕ) :
    (ws[i]?.getD []).length≤(encodeBitList ws).length := by
  induction ws generalizing i with
  | nil => simp [encodeBitList]
  | cons w ws ih =>
    cases i with
    | zero => simp [encodeBitList];omega
    | succ i =>
      have h := ih i
      simp only [List.getElem?_cons_succ] at *
      simp only [encodeBitList,List.length_cons,pairBits_length]
      omega

lemma encoded_set_length (ws : List BitString) (i : ℕ) (w : BitString) :
    (encodeBitList (ws.set i w)).length≤(encodeBitList ws).length+2*w.length := by
  induction ws generalizing i with
  | nil => simp [encodeBitList]
  | cons x xs ih =>
    cases i with
    | zero => simp [encodeBitList];omega
    | succ i =>
      have h := ih i
      simp only [List.set,encodeBitList,List.length_cons,pairBits_length]
      omega

lemma rowCheck_bound (ls hs : List BitString) (i : ℕ) (v : BitString) :
    RowCheck.bound ls hs i v≤200*((encodeBitList ls).length+(encodeBitList hs).length+i+v.length+1)^2 := by
  have hl := word_length_le_encoded ls i
  have hh := word_length_le_encoded hs i
  unfold RowCheck.bound GraphReduction.Runtime.lookupBound
  nlinarith

lemma arraySwap_bound (ws : List BitString) (i j : ℕ) :
    ArraySwap.bound ws i j≤200*((encodeBitList ws).length+i+j+1)^2 := by
  have ha := word_length_le_encoded ws i
  have hb := word_length_le_encoded ws j
  have hl := encoded_set_length ws i (ws[j]?.getD [])
  have hm := Nat.mul_le_mul_left j hl
  have hm' := Nat.mul_le_mul_left j hb
  unfold ArraySwap.bound WordArray.updateBound GraphReduction.Runtime.lookupBound
  dsimp only
  nlinarith

lemma switch_bound (ls hs ws : List BitString) (i j : ℕ) :
    Switch.bound ls hs ws i j≤1000*((encodeBitList ls).length+(encodeBitList hs).length+
      (encodeBitList ws).length+i+j+1)^2 := by
  have ha := word_length_le_encoded ws i
  have hb := word_length_le_encoded ws j
  have hl1 := word_length_le_encoded ls i
  have hl2 := word_length_le_encoded ls j
  have hh1 := word_length_le_encoded hs i
  have hh2 := word_length_le_encoded hs j
  have hs := arraySwap_bound ws i j
  unfold Switch.bound RowCheck.bound GraphReduction.Runtime.lookupBound
  nlinarith

end HiddenCircuits.Approximation.SamplerRuntime
