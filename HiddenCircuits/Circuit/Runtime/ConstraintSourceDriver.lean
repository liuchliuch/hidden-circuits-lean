import HiddenCircuits.Circuit.Runtime.ConstraintSourceFinish

/-! Proposition8.1 as a concrete ordinary-graph→native rational circuit-oracle
program, with literal zero-boundary generation and exact dyadic normalization. -/
namespace HiddenCircuits.Circuit.Runtime.ConstraintSource
open Complexity OracleBlock BinaryArithmetic Polynomial
set_option maxHeartbeats 1200000

noncomputable def prepare : OracleBlock 35 := seq SourceMetadata.program prepareQuery
noncomputable def called : OracleBlock 35 := seq prepare (OracleBlock.query 0 0)
noncomputable def program : OracleBlock 35 := seq called finish
noncomputable def prepareTime : Polynomial ℕ := SourceMetadata.time+42*X+36
noncomputable def calledTime : Polynomial ℕ := prepareTime+9*(X+prepareTime)+10
noncomputable def time : Polynomial ℕ := calledTime+finishTime.comp (X+calledTime)+2

noncomputable def responseStore {n : ℕ} (G : MatrixGraph n) : Store 35 :=
  SourceMetadata.outputStore (RationalOracleEncoding.bits (query G).value) (exponent G) n
    (forbidOccurrences (restoringIndependentProgram G).gates) (signOccurrences (restoringIndependentProgram G).gates)
lemma input_bound (raw : BitString) : ∀i : Fin 36,(Function.update (fun _ : Fin 36=>[]) 0 raw i).length ≤ raw.length := by
  intro i;simp only [Function.update_apply];split_ifs <;> simp

lemma prepare_executes (g : BitString→ℕ) {n : ℕ} (G : MatrixGraph n) :
    ∃c,prepare.Executes g (Function.update (fun _ : Fin 36=>[]) 0 (GraphInput.encode ⟨n,G⟩))
      (SourceMetadata.outputStore (query G).encode (exponent G) n
        (forbidOccurrences (restoringIndependentProgram G).gates) (signOccurrences (restoringIndependentProgram G).gates)) c ∧
      c ≤ prepareTime.eval (GraphInput.encode ⟨n,G⟩).length := by
  obtain ⟨c,hc,hb⟩:=SourceMetadata.program_executes g G
  have hp:=prepareQuery_executes g G
  have hn:=GraphInput.vertices_le_length (⟨n,G⟩:GraphInput)
  change n ≤ (GraphInput.encode ⟨n,G⟩).length at hn
  refine ⟨c+(42*n+34)+2,seq_executes _ _ g hc hp,?_⟩
  simp only [prepareTime,eval_add,eval_mul,eval_ofNat,eval_X]
  omega

lemma called_executes (g : BitString→ℕ) (hg : ConstraintOracle g) {n : ℕ} (G : MatrixGraph n) :
    ∃c,called.Executes g (Function.update (fun _ : Fin 36=>[]) 0 (GraphInput.encode ⟨n,G⟩))
      (responseStore G) c ∧ c ≤ calledTime.eval (GraphInput.encode ⟨n,G⟩).length := by
  obtain ⟨c,hc,hb⟩:=prepare_executes g G
  let s:=SourceMetadata.outputStore (query G).encode (exponent G) n
    (forbidOccurrences (restoringIndependentProgram G).gates) (signOccurrences (restoringIndependentProgram G).gates)
  have hq : (OracleBlock.query (0:Fin 36) 0).Executes g s (responseStore G)
      (1+(query G).encode.length+(RationalOracleEncoding.bits (query G).value).length) := by
    convert query_executes g (0:Fin 36) 0 s using 1
    · funext i
      simp only [OracleMachine.answerBits,show s 0=(query G).encode from rfl,hg (query G),RationalOracleEncoding.encode_code]
      fin_cases i <;> rfl
    · change 1+(query G).encode.length+(RationalOracleEncoding.bits (query G).value).length=
        1+(query G).encode.length+(Computability.encodeNat (g (query G).encode)).length
      rw [hg (query G),RationalOracleEncoding.encode_code]
  have hsize:=hc.stack_bound (input_bound (GraphInput.encode ⟨n,G⟩))
  have hquery : (query G).encode.length ≤ (GraphInput.encode ⟨n,G⟩).length+c := hsize (0:Fin 36)
  have ha : exponent G ≤ (GraphInput.encode ⟨n,G⟩).length+c := by
    have hh:=hsize (1:Fin 36)
    change (List.replicate (exponent G) true).length ≤ (GraphInput.encode ⟨n,G⟩).length+c at hh
    simpa only [List.length_replicate] using hh
  have hn:=GraphInput.vertices_le_length (⟨n,G⟩:GraphInput)
  change n ≤ (GraphInput.encode ⟨n,G⟩).length at hn
  have hr:=response_length G
  refine ⟨c+(1+(query G).encode.length+(RationalOracleEncoding.bits (query G).value).length)+2,
    seq_executes _ _ g hc hq,?_⟩
  simp only [calledTime,eval_add,eval_mul,eval_X,eval_ofNat]
  omega

lemma program_executes (g : BitString→ℕ) (hg : ConstraintOracle g) (G : GraphInput) :
    ∃c,program.Executes g (Function.update (fun _ : Fin 36=>[]) 0 G.encode)
      (Function.update (fun _ : Fin 36=>[]) 0 (Computability.encodeNat G.2.independentCount)) c ∧ c ≤ time.eval G.encode.length := by
  obtain ⟨n,G⟩:=G
  obtain ⟨c,hc,hb⟩:=called_executes g hg G
  have hs:=hc.stack_bound (input_bound (GraphInput.encode ⟨n,G⟩))
  change ∀i : Fin 36,(responseStore G i).length ≤ (GraphInput.encode ⟨n,G⟩).length+c at hs
  have hsame : responseStore G=finishStore (pairBits (signedBits (numerator G)) (signedBits 1)) (exponent G) n
      (forbidOccurrences (restoringIndependentProgram G).gates) (signOccurrences (restoringIndependentProgram G).gates) := by
    rw [responseStore,response_bits,initial_finishStore]
  obtain ⟨d,hd,hdb⟩:=finish_executes g (exponent G) n (forbidOccurrences (restoringIndependentProgram G).gates)
    (signOccurrences (restoringIndependentProgram G).gates) G.independentCount
    ((GraphInput.encode ⟨n,G⟩).length+c) (numerator G) rfl (by simpa only [←hsame] using hs)
  have hc' := hc
  rw [responseStore,response_bits] at hc'
  have he:=seq_executes _ _ g hc' hd
  have hm:=polynomial_nat_eval_mono finishTime (Nat.add_le_add_left hb (GraphInput.encode ⟨n,G⟩).length)
  dsimp only at hm
  refine ⟨c+d+2,?_,?_⟩
  · simpa only [responseStore,response_bits] using he
  · simp only [time,eval_add,eval_comp,eval_X,eval_ofNat]
    omega

theorem sharpPHard_of_oracle (g : BitString→ℕ) (hg : ConstraintOracle g) : SharpPHard g := by
  apply sharpPHard_of_canonical_independent_block g program time
  intro G
  obtain ⟨c,hc,hb⟩:=program_executes g hg G
  exact ⟨_,c,hc,Function.update_self _ _ _,hb⟩
theorem constraintEval_sharpPHard : SharpPHard constraintProblem := sharpPHard_of_oracle constraintProblem constraintProblem_oracle
end HiddenCircuits.Circuit.Runtime.ConstraintSource
