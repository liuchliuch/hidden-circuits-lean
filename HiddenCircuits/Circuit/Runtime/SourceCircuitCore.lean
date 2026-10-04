import HiddenCircuits.Circuit.Runtime.SourceCircuitScan

/-! Complete real source-circuit core: parse, emit the circuit header, prepare
all wires, scan/restore every edge, and reset all wires. -/
namespace HiddenCircuits.Circuit.Runtime.SourceCircuitEmitter
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock Polynomial

lemma circuitBits_header (n : ℕ) (gs : List (ConstraintGate n)) :
    circuitBits n gs=headerBits n++SourceScan.gateStream gs := by
  simp [circuitBits,headerBits,SourceScan.gateStream,pairBits_escape,escapeBits_replicate_true,List.append_assoc]

lemma restoring_circuit_stream {n : ℕ} (G : MatrixGraph n) :
    circuitBits n (restoringIndependentProgram G).gates =
      headerBits n++SourceScan.gateStream (preparationProgram n).gates++
        SourceScan.gateStream (restoringEdges (sourceEdges G)).gates++SourceScan.gateStream (resetProgram n).gates := by
  rw [circuitBits_header]
  simp only [restoringIndependentProgram,ConstraintProgram.compose,SourceScan.gateStream_append,List.append_assoc]

noncomputable def core : OracleBlock 35 := seq parseGraph (seq header (seq (uniform .copy) (seq scan (uniform .reset))))
noncomputable def coreTime : Polynomial ℕ := scanTime+28*X^2+183*X+46

theorem core_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixGraph n) :
    ∃ c, core.Executes g (Function.update (fun _ => []) 0 (GraphInput.encode ⟨n,G⟩))
      (store (n-1) (n-1) n G.bits (circuitBits n (restoringIndependentProgram G).gates).reverse
        (2*restoringSwapPairs (sourceEdges G))) c ∧ c≤coreTime.eval (GraphInput.encode ⟨n,G⟩).length := by
  let out₀ := (headerBits n).reverse
  let out₁ := (SourceScan.gateStream (preparationProgram n).gates).reverse++out₀
  let out₂ := (SourceScan.gateStream (restoringEdges (sourceEdges G)).gates).reverse++out₁
  let out₃ := (SourceScan.gateStream (resetProgram n).gates).reverse++out₂
  have h₀ := parseGraph_executes g G
  have h₁ : header.Executes g (store 0 0 n G.bits [] 0) (store 0 0 n G.bits out₀ 0) (14*n+8) := by
    simpa only [List.append_nil] using header_executes g 0 0 n G.bits [] 0
  obtain ⟨a,ha,hab⟩ := uniform_executes g .copy 0 0 n G.bits out₀ 0
  obtain ⟨b,hb,hbb⟩ := scan_executes g G out₁ 0
  obtain ⟨c,hc,hcb⟩ := uniform_executes g .reset (n-1) (n-1) n G.bits out₂ (2*restoringSwapPairs (sourceEdges G))
  have hstream : out₃=(circuitBits n (restoringIndependentProgram G).gates).reverse := by
    rw [restoring_circuit_stream]
    simp [out₃,out₂,out₁,out₀,List.reverse_append,List.append_assoc]
  have h₂ : (uniform .copy).Executes g (store 0 0 n G.bits out₀ 0) (store 0 0 n G.bits out₁ 0) a := ha
  have h₃ : scan.Executes g (store 0 0 n G.bits out₁ 0)
      (store (n-1) (n-1) n G.bits out₂ (2*restoringSwapPairs (sourceEdges G))) b := by
    simpa only [Nat.zero_add] using hb
  have h₄ : (uniform .reset).Executes g (store (n-1) (n-1) n G.bits out₂ (2*restoringSwapPairs (sourceEdges G)))
      (store (n-1) (n-1) n G.bits out₃ (2*restoringSwapPairs (sourceEdges G))) c := hc
  rw [hstream] at h₄
  refine ⟨_,seq_executes _ _ g h₀ (seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ h₄))),?_⟩
  have hn := GraphInput.vertices_le_length (⟨n,G⟩ : GraphInput)
  change n≤(GraphInput.encode ⟨n,G⟩).length at hn
  have hs := polynomial_nat_eval_mono scanTime hn
  dsimp only at hs
  have hp := Nat.pow_le_pow_left hn 2
  simp only [coreTime,eval_add,eval_mul,eval_pow,eval_X,eval_ofNat]
  omega

lemma core_queryFree : core.QueryFree := seq_queryFree _ _ parseGraph_queryFree
  (seq_queryFree _ _ header_queryFree (seq_queryFree _ _ (uniform_queryFree _) (seq_queryFree _ _ scan_queryFree (uniform_queryFree _))))

end HiddenCircuits.Circuit.Runtime.SourceCircuitEmitter
