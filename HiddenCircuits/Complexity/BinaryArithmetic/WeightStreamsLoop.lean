import HiddenCircuits.Complexity.BinaryArithmetic.WeightStreamsBody

/-! The actual degree-controlled loop visits every consecutive node exactly once. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic
open OracleBlock

 noncomputable def weightStreamLoop : OracleBlock 16 := whilePop 14 weightStreamBody weightStreamBody

 theorem weightStreamLoop_executes (g : BitString → ℕ) (d i m : ℕ) (him : i+m≤d+1)
    (outD outN : BitString) :
    ∃ t, weightStreamLoop.Executes g
      (weightStreamStore i (d-i) [] [] (List.replicate m true) outD outN)
      (weightStreamStore (i+m) (d-(i+m)) [] [] []
        ((encodeBitList ((List.range' i m).map (denominatorAt d))).reverse++outD)
        ((encodeBitList ((List.range' i m).map (negativeNumeratorAt d))).reverse++outN)) t ∧
      t ≤ m*weightStreamBodyTime.eval d+1 := by
  suffices ∃ t, WhileExecution (14 : Fin 17) weightStreamBody weightStreamBody g
      (weightStreamStore i (d-i) [] [] (List.replicate m true) outD outN)
      (weightStreamStore (i+m) (d-(i+m)) [] [] []
        ((encodeBitList ((List.range' i m).map (denominatorAt d))).reverse++outD)
        ((encodeBitList ((List.range' i m).map (negativeNumeratorAt d))).reverse++outN)) t ∧
      t ≤ m*weightStreamBodyTime.eval d+1 by
    obtain ⟨t,ht,hbound⟩ := this
    exact ⟨t,whilePop_executes _ _ _ g ht,hbound⟩
  induction m generalizing i outD outN with
  | zero =>
    refine ⟨1,?_,by simp⟩
    simpa [encodeBitList] using (WhileExecution.empty
      (stack := (14 : Fin 17)) (B := weightStreamBody) (C := weightStreamBody)
      (g := g) (weightStreamStore i (d-i) [] [] [] outD outN) rfl)
  | succ m ih =>
    have hi : i<d+1 := by omega
    obtain ⟨b,hb,hbb⟩ := weightStreamBody_executes g d i hi (List.replicate m true) outD outN
    obtain ⟨t,ht,htb⟩ := ih (i+1) (by omega)
      ((wordChunk (denominatorAt d i)).reverse++outD)
      ((wordChunk (negativeNumeratorAt d i)).reverse++outN)
    have hs : Function.update (weightStreamStore i (d-i) [] [] (List.replicate (m+1) true) outD outN)
        14 (List.replicate m true) = weightStreamStore i (d-i) [] [] (List.replicate m true) outD outN := by
      funext j; fin_cases j <;> rfl
    rw [← hs] at hb
    have h := WhileExecution.one
      (show weightStreamStore i (d-i) [] [] (List.replicate (m+1) true) outD outN 14 =
        true::List.replicate m true from rfl) hb ht
    refine ⟨1+b+1+t,?_,?_⟩
    · have he : i+1+m=i+(m+1) := by omega
      simpa [he,List.range'_succ,encodeBitList_eq_chunks,List.reverse_append,List.append_assoc] using h
    · nlinarith

 def denominatorWords (d : ℕ) : List BitString :=
  (List.finRange (d+1)).map (fun i => signedBits (interpolationDenominator d i))
 def negativeNumeratorWords (d : ℕ) : List BitString :=
  (List.finRange (d+1)).map (fun i => signedBits (interpolationNegativeNumerator d i))

 theorem denominatorWords_range (d : ℕ) :
    denominatorWords d = (List.range (d+1)).map (denominatorAt d) := by
  rw [← List.map_coe_finRange_eq_range]
  simp only [List.map_map,denominatorWords]
  apply List.map_congr_left
  intro i _
  simp [Function.comp_def,denominatorAt,i.isLt]

 theorem negativeNumeratorWords_range (d : ℕ) :
    negativeNumeratorWords d = (List.range (d+1)).map (negativeNumeratorAt d) := by
  rw [← List.map_coe_finRange_eq_range]
  simp only [List.map_map,negativeNumeratorWords]
  apply List.map_congr_left
  intro i _
  simp [Function.comp_def,negativeNumeratorAt,i.isLt]

 theorem encodedWords_length_le (xs : List BitString) (B : ℕ) (h : ∀ x∈xs, x.length≤B) :
    (encodeBitList xs).length ≤ xs.length*(2*B+2) := by
  induction xs with
  | nil => simp [encodeBitList]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [encodeBitList,List.length_cons,pairBits_length]
    nlinarith

 theorem denominatorWords_length_bound (d : ℕ) :
    (encodeBitList (denominatorWords d)).length ≤ (d+1)*(2*weightWordBound d+2) := by
  rw [denominatorWords_range]
  have h := encodedWords_length_le ((List.range (d+1)).map (denominatorAt d)) (weightWordBound d) (by
    intro x hx
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
    exact denominatorAt_length d j)
  simpa using h

 theorem negativeNumeratorWords_length_bound (d : ℕ) :
    (encodeBitList (negativeNumeratorWords d)).length ≤ (d+1)*(2*weightWordBound d+2) := by
  rw [negativeNumeratorWords_range]
  have h := encodedWords_length_le ((List.range (d+1)).map (negativeNumeratorAt d)) (weightWordBound d) (by
    intro x hx
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
    exact negativeNumeratorAt_length d j)
  simpa using h

 theorem weightStreamLoop_all (g : BitString → ℕ) (d : ℕ) :
    ∃ t, weightStreamLoop.Executes g (weightStreamStore 0 d [] [] (List.replicate (d+1) true) [] [])
      (weightStreamStore (d+1) 0 [] [] [] (encodeBitList (denominatorWords d)).reverse
        (encodeBitList (negativeNumeratorWords d)).reverse) t ∧
      t ≤ (d+1)*weightStreamBodyTime.eval d+1 := by
  simpa [← List.range_eq_range',← denominatorWords_range,← negativeNumeratorWords_range] using
    weightStreamLoop_executes g d 0 (d+1) (by omega) [] []

 lemma weightStreamLoop_queryFree : weightStreamLoop.QueryFree :=
  whilePop_queryFree _ _ _ weightStreamBody_queryFree weightStreamBody_queryFree

end HiddenCircuits.Complexity.BinaryArithmetic
