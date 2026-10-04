import HiddenCircuits.GraphReduction.Runtime.MonotoneCallback

/-! Exact binary graph queries emitted from structural monotone descriptors. -/
namespace HiddenCircuits.GraphReduction.Runtime
open Complexity Complexity.OracleBlock

lemma recordEdge_monotone {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ)
    (i j : Fin (monotoneGraphInput pairs S T s).1) :
    recordEdge (monotoneRecords pairs S T s) i.val j.val=(monotoneGraphInput pairs S T s).2.edge i j := by
  have hi : i.val<(monotoneEnumeration S T s).labels.length := i.isLt
  have hj : j.val<(monotoneEnumeration S T s).labels.length := j.isLt
  simp only [recordEdge,monotoneRecords,List.getElem?_map,List.getElem?_eq_getElem,hi,hj,
    Option.map_some,Option.getD_some]
  exact monotoneRecord_edge pairs S T s i j

noncomputable def monotoneEmitter : OracleBlock 56 := MatrixEmitter.block monotoneCallback

/-- All adjacency bits are computed by the actual fixed callback; the resulting
bytes are exactly the existing boundary-retained, unweighted graph query. -/
theorem monotoneEmitter_executes {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ)
    (g : BitString → ℕ) :
    ∃ c, monotoneEmitter.Executes g
      (MatrixEmitter.store (k := 49) (monotoneGraphInput pairs S T s).1 0 0 [] [] [] []
        (callbackParams (monotoneDescriptor pairs S T s)))
      (Function.update
        (MatrixEmitter.store (k := 49) (monotoneGraphInput pairs S T s).1 0 0 [] [] [] []
          (callbackParams (monotoneDescriptor pairs S T s))) (MatrixEmitter.port 7)
        (monotoneGraphInput pairs S T s).encode) c ∧
      c≤(monotoneGraphInput pairs S T s).1*(monotoneGraphInput pairs S T s).1*
        (callbackBound (monotoneGraphInput pairs S T s).1 (monotoneDescriptor pairs S T s).length+18)+
        40*(monotoneGraphInput pairs S T s).1+30 := by
  apply MatrixEmitter.graph_executes (monotoneGraphInput pairs S T s).2 monotoneCallback
    (recordEdge (monotoneRecords pairs S T s)) (recordEdge_monotone pairs S T s)
    (callbackBound (monotoneGraphInput pairs S T s).1 (monotoneDescriptor pairs S T s).length)
    (callbackParams (monotoneDescriptor pairs S T s)) ?_ g
  intro g i j out inner outer hi hj
  have hn := monotoneRecords_length pairs S T s
  have hi' : i<(monotoneRecords pairs S T s).length := by omega
  have hj' : j<(monotoneRecords pairs S T s).length := by omega
  simpa only [hn,monotoneDescriptor] using
    monotoneCallback_framed g (monotoneRecords pairs S T s) i j hi' hj' out inner outer

noncomputable def graphQueryTime : Polynomial ℕ := 5000*(Polynomial.X+1)^4

lemma graphQueryTime_bound (n L : ℕ) :
    n*n*(callbackBound n L+18)+40*n+30≤graphQueryTime.eval (n+L) := by
  let M := n+L
  have hn : n≤M := by dsimp [M]; omega
  have hL : L≤M := by dsimp [M]; omega
  calc
    _ ≤ M*M*(callbackBound M M+18)+40*M+30 := by
      unfold callbackBound lookupBound
      gcongr
    _ ≤ _ := by
      change _ ≤ graphQueryTime.eval M
      simp only [graphQueryTime,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,
        Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
      unfold callbackBound lookupBound
      ring_nf
      omega

theorem monotoneEmitter_polynomial {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ)
    (g : BitString → ℕ) :
    ∃ c, monotoneEmitter.Executes g
      (MatrixEmitter.store (k := 49) (monotoneGraphInput pairs S T s).1 0 0 [] [] [] []
        (callbackParams (monotoneDescriptor pairs S T s)))
      (Function.update
        (MatrixEmitter.store (k := 49) (monotoneGraphInput pairs S T s).1 0 0 [] [] [] []
          (callbackParams (monotoneDescriptor pairs S T s))) (MatrixEmitter.port 7)
        (monotoneGraphInput pairs S T s).encode) c ∧
      c≤graphQueryTime.eval ((monotoneGraphInput pairs S T s).1+(monotoneDescriptor pairs S T s).length) := by
  obtain ⟨c,hc,hb⟩ := monotoneEmitter_executes pairs S T s g
  exact ⟨c,hc,hb.trans (graphQueryTime_bound _ _)⟩


lemma monotoneEmitter_queryFree : monotoneEmitter.QueryFree :=
  MatrixEmitter.block_queryFree _ monotoneCallback_queryFree

lemma encoded_records_length_le (records : List VertexRecord) (B : ℕ)
    (hB : ∀ v∈records, (encodeVertex v).length≤B) :
    (encodeBitList (records.map encodeVertex)).length≤records.length*(2*B+2) := by
  induction records with
  | nil => simp [encodeBitList]
  | cons v vs ih =>
    have hv := hB v (by simp)
    have ht := ih (fun w hw => hB w (by simp [hw]))
    simp only [List.map_cons,encodeBitList,List.length_cons,pairBits_length]
    nlinarith

 theorem monotoneDescriptor_size {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) :
    (monotoneDescriptor pairs S T s).length≤
      (monotoneGraphInput pairs S T s).1*(18+4*h+12*p+4*s) := by
  have hb := encoded_records_length_le (monotoneRecords pairs S T s) (8+2*h+6*p+2*s) (by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
    exact encoded_record_bound pairs S T w)
  rw [monotoneRecords_length] at hb
  simpa only [monotoneDescriptor,show 2*(8+2*h+6*p+2*s)+2=18+4*h+12*p+4*s by omega] using hb

 theorem monotoneEmitter_runs {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ)
    (g : BitString → ℕ) :
    ∃ (c : monotoneEmitter.machine.Config) (t : ℕ), monotoneEmitter.machine.Runs g
      (monotoneEmitter.config monotoneEmitter.start
        (MatrixEmitter.store (k := 49) (monotoneGraphInput pairs S T s).1 0 0 [] [] [] []
          (callbackParams (monotoneDescriptor pairs S T s)))) c t ∧
      c.stack = Function.update
        (MatrixEmitter.store (k := 49) (monotoneGraphInput pairs S T s).1 0 0 [] [] [] []
          (callbackParams (monotoneDescriptor pairs S T s))) (MatrixEmitter.port 7)
        (monotoneGraphInput pairs S T s).encode ∧
      t≤graphQueryTime.eval ((monotoneGraphInput pairs S T s).1+(monotoneDescriptor pairs S T s).length) := by
  obtain ⟨t,ht,hb⟩ := monotoneEmitter_polynomial pairs S T s g
  refine ⟨monotoneEmitter.config monotoneEmitter.exit
    (Function.update
      (MatrixEmitter.store (k := 49) (monotoneGraphInput pairs S T s).1 0 0 [] [] [] []
        (callbackParams (monotoneDescriptor pairs S T s))) (MatrixEmitter.port 7)
      (monotoneGraphInput pairs S T s).encode),t,?_,rfl,hb⟩
  apply (OracleMachine.runs_iff_steps_halt _).mpr
  exact ⟨ht,by simp [OracleMachine.step,machine,config,monotoneEmitter.exit_halt]⟩

end HiddenCircuits.GraphReduction.Runtime
