import HiddenCircuits.Complexity.SourceGrid.Ports

/-! Literal clone-query emission, charged oracle access, and attaching the
canonical nonnegative sign to the returned natural count. -/
namespace HiddenCircuits.Complexity.SourceGrid
open OracleBlock BinaryArithmetic

noncomputable def emitQuery (Q : OracleBlock 29) : OracleBlock 42 := rename Q queryEmbedding

theorem emitQuery_executes (Q : OracleBlock 29) (g : BitString → ℕ)
    (n m i j : ℕ) (inner outer query : BitString) (v : Values) (hv : v.value=[]) (c : ℕ)
    (hQ : Q.Executes g (queryStore v.formula i j []) (queryStore v.formula i j query) c) :
    (emitQuery Q).Executes g (store n m i j inner outer v)
      (store n m i j inner outer {v with value:=query}) c := by
  apply rename_executes_to Q queryEmbedding g hQ
  · rw [restrict_query,hv]
  · exact restrict_query _ _ _ _ _ _ _
  · intro q hq
    rw [←update_value]
    exact Function.update_of_ne (hq 7).symm _ _

noncomputable def askQuery : OracleBlock 42 := seq (query 15 15) (push 15 false)

lemma signedBits_nat (z : ℕ) : signedBits (z : ℤ)=false::Computability.encodeNat z := by
  simp [signedBits,negative]

theorem askQuery_executes (g : BitString → ℕ) (n m i j : ℕ) (inner outer : BitString) (v : Values) :
    askQuery.Executes g (store n m i j inner outer v)
      (store n m i j inner outer {v with value:=signedBits (g v.value : ℤ)})
      (v.value.length+(Computability.encodeNat (g v.value)).length+4) := by
  have h₀ : (query (15 : Fin 43) 15).Executes g (store n m i j inner outer v)
      (store n m i j inner outer {v with value:=Computability.encodeNat (g v.value)})
      (1+v.value.length+(Computability.encodeNat (g v.value)).length) := by
    simpa only [update_value] using query_executes g (15 : Fin 43) 15 (store n m i j inner outer v)
  have h₁ : (push (15 : Fin 43) false).Executes g
      (store n m i j inner outer {v with value:=Computability.encodeNat (g v.value)})
      (store n m i j inner outer {v with value:=signedBits (g v.value : ℤ)}) 1 := by
    simpa only [update_value,signedBits_nat] using push_executes g (15 : Fin 43) false
      (store n m i j inner outer {v with value:=Computability.encodeNat (g v.value)})
  convert seq_executes _ _ g h₀ h₁ using 1 <;> omega

end HiddenCircuits.Complexity.SourceGrid
