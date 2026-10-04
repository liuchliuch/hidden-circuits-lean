import HiddenCircuits.Complexity.CanonicalSubstitution.QueryCall
import HiddenCircuits.Complexity.CanonicalSubstitution.GridStores
import HiddenCircuits.Complexity.CNFCloneEmitter.Runtime

/-! Actual source grid body with every independent-set oracle call replaced by
finite target-oracle solver code on a proved canonical graph query. -/
namespace HiddenCircuits.Complexity.CanonicalSubstitution
open OracleBlock BinaryArithmetic BinaryArithmetic.RegisterMachine Polynomial
variable {k : ℕ}

noncomputable def body (C : OracleBlock k) : OracleBlock (k+43) :=
  seq (liftBase (SourceGrid.emitQuery CNFCloneEmitter.program)) (seq (call C) (liftBase SourceGrid.calculate))
noncomputable def cellTime (q : Polynomial ℕ) : Polynomial ℕ :=
  CNFCloneEmitter.timeBound.comp (3*X)+(cleanSolverTime (k := k) q).comp (X^4)+6*X^4+6*X^2+
    GridWeightsRuntime.time.comp (2*X)+GridTermRuntime.time.comp (8*(X+1)^3)+40*(X+1)^3+41

theorem body_executes (C : OracleBlock k) (q : Polynomial ℕ) (g : BitString → ℕ)
    (hC : ∀ G : GraphInput, ∃ s : Store k, ∃ c,
      C.Executes g (Function.update (fun _ => []) 0 (GraphInput.encode G)) s c ∧
      s 0=Computability.encodeNat G.2.independentCount ∧ c≤q.eval (GraphInput.encode G).length)
    (F : CNFInput) (i : Fin (F.1+1)) (j : Fin (F.2.1+1))
    (indices : List (Fin (F.1+1) × Fin (F.2.1+1))) (hlen : indices.length≤(F.1+1)*(F.2.1+1))
    (inner outer : BitString) :
    let acc := gridPartialSum F.1 F.2.1 (fun a b => (F.2.2.cloneCount a.val b.val : ℤ)) indices
    ∃ c, (body C).Executes g
      (extend (SourceGrid.store F.1 F.2.1 i.val j.val inner outer (SourceGrid.persistent F acc)))
      (extend (SourceGrid.store F.1 F.2.1 i.val j.val inner outer
        (SourceGrid.persistent F (acc+gridTerm F.1 F.2.1 i j (F.2.2.cloneCount i.val j.val))))) c ∧
      c≤(cellTime (k := k) q).eval (CNFInput.encode F).length := by
  dsimp only
  let acc := gridPartialSum F.1 F.2.1 (fun a b => (F.2.2.cloneCount a.val b.val : ℤ)) indices
  let value := F.2.2.cloneCount i.val j.val
  let L := (CNFInput.encode F).length
  let B := CNFInput.gridRegisterBound L
  let v₀ := SourceGrid.persistent F acc
  let v₁ : SourceGrid.Values := {v₀ with value:=F.2.2.encodedCloneQuery i.val j.val}
  let v₂ : SourceGrid.Values := {v₀ with value:=signedBits (value : ℤ)}
  obtain ⟨e,he,heb⟩ := CNFCloneEmitter.program_executes g F.2.2 i.val j.val
  have h₀ := liftBase_executes (k := k) (SourceGrid.emitQuery CNFCloneEmitter.program) g _ _ _
    (SourceGrid.emitQuery_executes CNFCloneEmitter.program g F.1 F.2.1 i.val j.val inner outer
      (F.2.2.encodedCloneQuery i.val j.val) v₀ rfl e he)
  obtain ⟨a,ha,hab⟩ := call_executes C q g hC
    (SourceGrid.store F.1 F.2.1 i.val j.val inner outer v₁) (F.2.2.cloneQuery i.val j.val) rfl rfl
  have h₁ : (call C).Executes g
      (extend (SourceGrid.store F.1 F.2.1 i.val j.val inner outer v₁))
      (extend (SourceGrid.store F.1 F.2.1 i.val j.val inner outer v₂)) a := by
    simpa only [SourceGrid.update_value,CNF.cloneQuery_count] using ha
  have hb : Bounded B (GridTermRuntime.registers (gridDenominator F.1 F.2.1) (interpolationDenominator F.1 i)
      (interpolationDenominator F.2.1 j) (interpolationNegativeNumerator F.2.1 j) value acc 0) := by
    simpa only [CNF.encodedCloneQuery_correct] using CNFInput.grid_registers_bounded F i j indices hlen
  have ht : (signedBits (gridTerm F.1 F.2.1 i j (value : ℤ))).length≤B := by
    have hs := CNFInput.grid_registers_bounded F i j [(i,j)] (by simp only [List.length_cons,List.length_nil];nlinarith)
    have hh := hs 5
    change (signedBits (gridPartialSum F.1 F.2.1 (fun a b => (F.2.2.cloneCount a.val b.val : ℤ)) [(i,j)])).length≤B at hh
    simpa only [gridPartialSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using hh
  obtain ⟨b,hbRun,hbb⟩ := SourceGrid.calculate_executes g F.1 F.2.1 i j inner outer (CNFInput.encode F) value acc B hb ht
  have h₂ := liftBase_executes (k := k) SourceGrid.calculate g _ _ _ hbRun
  refine ⟨e+(a+b+2)+2,seq_executes _ _ g h₀ (seq_executes _ _ g h₁ h₂),?_⟩
  have hlenF := CNFInput.encode_length_lower F
  have hin : i.val≤F.1 := by omega
  have hjm : j.val≤F.2.1 := by omega
  have hq := polynomial_nat_eval_mono CNFCloneEmitter.timeBound (show L+i.val+j.val≤3*L by dsimp [L];omega)
  have hw := polynomial_nat_eval_mono GridWeightsRuntime.time (show F.1+F.2.1≤2*L by dsimp [L];omega)
  dsimp only at hq hw
  have hqlen := CNFInput.query_length_in_source_bits F i j
  have hsolver := polynomial_nat_eval_mono (cleanSolverTime (k := k) q) hqlen
  dsimp only at hsolver
  have hal := F.2.2.encodedCloneAnswer_grid_length i j
  rw [CNF.encodedCloneQuery_correct] at hal
  have hvalSize : (2*F.1+F.2.1)^2+1≤L^2 := by
    have hh : 2*F.1+F.2.1+1≤L := hlenF
    nlinarith
  change e≤CNFCloneEmitter.timeBound.eval (L+i.val+j.val) at heb
  change a≤(cleanSolverTime (k := k) q).eval (F.2.2.encodedCloneQuery i.val j.val).length+
    6*(F.2.2.encodedCloneQuery i.val j.val).length+
    6*(Computability.encodeNat (F.2.2.cloneQuery i.val j.val).2.independentCount).length+17 at hab
  rw [CNF.cloneQuery_count] at hab
  simp only [cellTime,eval_add,eval_comp,eval_mul,eval_pow,eval_X,eval_ofNat,eval_one]
  dsimp only [B,CNFInput.gridRegisterBound,L,value] at *
  omega

end HiddenCircuits.Complexity.CanonicalSubstitution
