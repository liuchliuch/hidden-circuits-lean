import HiddenCircuits.Complexity.SourceGrid.Query
import HiddenCircuits.Complexity.SourceGrid.Calculate

/-! The complete fixed source-grid body. Its emitter parameter is actual finite
code; the canonical clone emitter supplies the displayed operational premise. -/
namespace HiddenCircuits.Complexity.SourceGrid
open OracleBlock BinaryArithmetic BinaryArithmetic.RegisterMachine Polynomial

noncomputable def body (Q : OracleBlock 29) : OracleBlock 42 :=
  seq (emitQuery Q) (seq askQuery calculate)
noncomputable def cellTime (q : Polynomial ℕ) : Polynomial ℕ :=
  q.comp (3*X)+X^4+X^2+GridWeightsRuntime.time.comp (2*X)+
    GridTermRuntime.time.comp (8*(X+1)^3)+40*(X+1)^3+30

def persistent (F : CNFInput) (acc : ℤ) : Values :=
  {formula:=CNFInput.encode F,denominator:=signedBits (gridDenominator F.1 F.2.1),accumulator:=signedBits acc}

theorem body_executes (Q : OracleBlock 29) (q : Polynomial ℕ)
    (hQ : ∀ (F : CNFInput) (a b : ℕ), ∃ c,
      Q.Executes GraphInput.independentSetProblem (queryStore (CNFInput.encode F) a b [])
        (queryStore (CNFInput.encode F) a b (F.2.2.encodedCloneQuery a b)) c ∧
      c≤q.eval ((CNFInput.encode F).length+a+b))
    (F : CNFInput) (i : Fin (F.1+1)) (j : Fin (F.2.1+1))
    (indices : List (Fin (F.1+1) × Fin (F.2.1+1))) (hlen : indices.length≤(F.1+1)*(F.2.1+1))
    (inner outer : BitString) :
    let acc := gridPartialSum F.1 F.2.1 (fun a b => (F.2.2.cloneCount a.val b.val : ℤ)) indices
    ∃ c, (body Q).Executes GraphInput.independentSetProblem
      (store F.1 F.2.1 i.val j.val inner outer (persistent F acc))
      (store F.1 F.2.1 i.val j.val inner outer
        (persistent F (acc+gridTerm F.1 F.2.1 i j (F.2.2.cloneCount i.val j.val)))) c ∧
      c≤(cellTime q).eval (CNFInput.encode F).length := by
  dsimp only
  let acc := gridPartialSum F.1 F.2.1 (fun a b => (F.2.2.cloneCount a.val b.val : ℤ)) indices
  let value := F.2.2.cloneCount i.val j.val
  let L := (CNFInput.encode F).length
  let B := CNFInput.gridRegisterBound L
  let v₀ := persistent F acc
  let v₁ : Values := {v₀ with value:=F.2.2.encodedCloneQuery i.val j.val}
  let v₂ : Values := {v₀ with value:=signedBits (value : ℤ)}
  obtain ⟨e,he,heb⟩ := hQ F i.val j.val
  have h₀ := emitQuery_executes Q GraphInput.independentSetProblem F.1 F.2.1 i.val j.val inner outer
    (F.2.2.encodedCloneQuery i.val j.val) v₀ rfl e he
  have h₁ : askQuery.Executes GraphInput.independentSetProblem (store F.1 F.2.1 i.val j.val inner outer v₁)
      (store F.1 F.2.1 i.val j.val inner outer v₂)
      ((F.2.2.encodedCloneQuery i.val j.val).length+(Computability.encodeNat value).length+4) := by
    have hh := askQuery_executes GraphInput.independentSetProblem F.1 F.2.1 i.val j.val inner outer v₁
    dsimp only [v₁] at hh
    rw [CNF.encodedCloneQuery_correct] at hh
    exact hh
  have hb : Bounded B (GridTermRuntime.registers (gridDenominator F.1 F.2.1) (interpolationDenominator F.1 i)
      (interpolationDenominator F.2.1 j) (interpolationNegativeNumerator F.2.1 j) value acc 0) := by
    simpa only [CNF.encodedCloneQuery_correct] using CNFInput.grid_registers_bounded F i j indices hlen
  have ht : (signedBits (gridTerm F.1 F.2.1 i j (value : ℤ))).length≤B := by
    have hs := CNFInput.grid_registers_bounded F i j [(i,j)] (by simp only [List.length_cons,List.length_nil];nlinarith)
    have hh := hs 5
    change (signedBits (gridPartialSum F.1 F.2.1
      (fun a b => (F.2.2.cloneCount a.val b.val : ℤ)) [(i,j)])).length≤B at hh
    simpa only [gridPartialSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using hh
  obtain ⟨a,ha,hab⟩ := calculate_executes GraphInput.independentSetProblem F.1 F.2.1 i j
    inner outer (CNFInput.encode F) value acc B hb ht
  refine ⟨_,seq_executes _ _ _ h₀ (seq_executes _ _ _ h₁ ha),?_⟩
  have hlenF := CNFInput.encode_length_lower F
  have hin : i.val≤F.1 := by omega
  have hjm : j.val≤F.2.1 := by omega
  have hq := polynomial_nat_eval_mono q (show L+i.val+j.val≤3*L by dsimp [L];omega)
  have hw := polynomial_nat_eval_mono GridWeightsRuntime.time (show F.1+F.2.1≤2*L by dsimp [L];omega)
  dsimp only at hq hw
  have hqlen := CNFInput.query_length_in_source_bits F i j
  have hal := F.2.2.encodedCloneAnswer_grid_length i j
  rw [CNF.encodedCloneQuery_correct] at hal
  have hvalSize : (2*F.1+F.2.1)^2+1≤L^2 := by
    have hh : 2*F.1+F.2.1+1≤L := hlenF
    nlinarith
  simp only [cellTime,eval_add,eval_comp,eval_mul,eval_pow,eval_X,eval_ofNat,eval_one]
  dsimp only [B,CNFInput.gridRegisterBound,L,value] at *
  omega

end HiddenCircuits.Complexity.SourceGrid
