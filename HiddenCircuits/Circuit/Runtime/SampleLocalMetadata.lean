import HiddenCircuits.Circuit.Runtime.SampleLocalLoops
import HiddenCircuits.Circuit.Runtime.SampleScalar

/-! Actual unary dyadic-exponent and sign bookkeeping for sampled local words. -/
namespace HiddenCircuits.Circuit.Runtime.SampleLocalEmitter
open HiddenCircuits.Complexity OracleBlock

noncomputable def addExponent (coefficient constant : ℕ) : OracleBlock 8 :=
  seq (copyOn 1 7 8 (by decide) (by decide) (by decide))
    (seq (repeatPrepend 7 3 (List.replicate coefficient true)) (prepend 3 (List.replicate constant true)))

theorem addExponent_executes (g : BitString → ℕ) (a b p u : ℕ) (out exponent sign : BitString) :
    (addExponent a b).Executes g (store p u 0 out exponent sign [] [] [])
      (store p u 0 out (List.replicate (a*u+b) true++exponent) sign [] [] []) ((3*a+8)*u+3*b+8) := by
  have hc : (copyOn (1:Fin 9) 7 8 (by decide) (by decide) (by decide)).Executes g
      (store p u 0 out exponent sign [] [] []) (store p u u out exponent sign [] [] []) (5*u+2) := by
    convert copyOn_executes g (1:Fin 9) 7 8 (by decide) (by decide) (by decide)
      (store p u 0 out exponent sign [] [] []) rfl using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  have hr : (repeatPrepend (7:Fin 9) 3 (List.replicate a true)).Executes g
      (store p u u out exponent sign [] [] [])
      (store p u 0 out (List.replicate (a*u) true++exponent) sign [] [] []) ((3*a+3)*u+1) := by
    convert repeatPrepend_executes g (7:Fin 9) 3 (by decide) (List.replicate a true)
      (store p u u out exponent sign [] [] []) using 1
    · funext i;fin_cases i <;> simp [store,List.flatten_replicate_replicate,Nat.mul_comm]
    · simp [store]
  have hp : (prepend (3:Fin 9) (List.replicate b true)).Executes g
      (store p u 0 out (List.replicate (a*u) true++exponent) sign [] [] [])
      (store p u 0 out (List.replicate (a*u+b) true++exponent) sign [] [] []) (3*b+1) := by
    convert prepend_executes g (3:Fin 9) (List.replicate b true)
      (store p u 0 out (List.replicate (a*u) true++exponent) sign [] [] []) using 1
    · funext i;fin_cases i <;> simp [store,←List.append_assoc,←List.replicate_add,Nat.add_comm]
    · simp
  convert seq_executes _ _ g hc (seq_executes _ _ g hr hp) using 1 <;> nlinarith

lemma addExponent_queryFree (a b : ℕ) : (addExponent a b).QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (repeatPrepend_queryFree _ _ _) (prepend_queryFree _ _))

noncomputable def negate : OracleBlock 8 := branchPop 4 skip (push 4 true) (push 4 false)

theorem negate_executes (g : BitString → ℕ) (p u : ℕ) (out exponent : BitString) (negative : Bool) :
    negate.Executes g (store p u 0 out exponent [negative] [] [] [])
      (store p u 0 out exponent [!negative] [] [] []) 3 := by
  have he : Function.update (store p u 0 out exponent [negative] [] [] []) 4 []=
      store p u 0 out exponent [] [] [] [] := by funext i;fin_cases i <;> rfl
  have hp (b : Bool) : (push (4:Fin 9) b).Executes g (store p u 0 out exponent [] [] [] [])
      (store p u 0 out exponent [b] [] [] []) 1 := by
    convert push_executes g (4:Fin 9) b (store p u 0 out exponent [] [] [] []) using 1
    funext i;fin_cases i <;> rfl
  cases negative
  · exact branchPop_false _ _ _ _ g rfl (by simpa only [he] using hp true)
  · exact branchPop_true _ _ _ _ g rfl (by simpa only [he] using hp false)

lemma negate_queryFree : negate.QueryFree := branchPop_queryFree _ _ _ _ skip_queryFree (push_queryFree _ _) (push_queryFree _ _)

noncomputable def oneMetadata (a : OneGate) : OracleBlock 8 :=
  seq (prepend 3 (List.replicate (SampleScalar.oneExponent a) true)) (if a=.hadamard then negate else skip)
def oneNegative (a : OneGate) (negative : Bool) : Bool := if a=.hadamard then !negative else negative
def oneMetadataCost (a : OneGate) : ℕ := 3*SampleScalar.oneExponent a+(if a=.hadamard then 6 else 4)

theorem oneMetadata_executes (g : BitString → ℕ) (a : OneGate) (p u : ℕ)
    (out exponent : BitString) (negative : Bool) :
    (oneMetadata a).Executes g (store p u 0 out exponent [negative] [] [] [])
      (store p u 0 out (List.replicate (SampleScalar.oneExponent a) true++exponent)
        [oneNegative a negative] [] [] []) (oneMetadataCost a) := by
  have hp : (prepend (3:Fin 9) (List.replicate (SampleScalar.oneExponent a) true)).Executes g
      (store p u 0 out exponent [negative] [] [] [])
      (store p u 0 out (List.replicate (SampleScalar.oneExponent a) true++exponent) [negative] [] [] [])
      (3*SampleScalar.oneExponent a+1) := by
    convert prepend_executes g (3:Fin 9) (List.replicate (SampleScalar.oneExponent a) true)
      (store p u 0 out exponent [negative] [] [] []) using 1
    · funext i;fin_cases i <;> rfl
    · simp
  by_cases ha : a=.hadamard
  · have hn := negate_executes g p u out (List.replicate (SampleScalar.oneExponent a) true++exponent) negative
    simpa [oneMetadata,oneNegative,oneMetadataCost,ha,Nat.add_assoc] using seq_executes _ _ g hp hn
  · have hn := skip_executes g (store p u 0 out (List.replicate (SampleScalar.oneExponent a) true++exponent) [negative] [] [] [])
    simpa [oneMetadata,oneNegative,oneMetadataCost,ha,Nat.add_assoc] using seq_executes _ _ g hp hn

lemma oneMetadata_queryFree (a : OneGate) : (oneMetadata a).QueryFree := by
  apply seq_queryFree _ _ (prepend_queryFree _ _)
  split_ifs
  · exact negate_queryFree
  · exact skip_queryFree

end HiddenCircuits.Circuit.Runtime.SampleLocalEmitter
