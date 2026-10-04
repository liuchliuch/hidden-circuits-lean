import HiddenCircuits.Circuit.Runtime.NativeConstraintCall
import HiddenCircuits.Circuit.Runtime.ConstraintSourceDriver

/-! Actual source #IS code calling an arbitrary concrete clean native N/CZ
solver. Metadata is kept in the low bank and is normalized by the existing
exact dyadic quotient program after the physically framed solver returns. -/
namespace HiddenCircuits.Circuit.Runtime.NativeConstraintSource
open Complexity OracleBlock BinaryArithmetic Polynomial
open NativeConstraintCall
set_option maxHeartbeats 1200000

noncomputable def called {k : ℕ} (S : OracleBlock k) : OracleBlock (k+36) :=
  seq (rename ConstraintSource.prepare (lowEmbedding k)) (NativeConstraintCall.program S)
noncomputable def program {k : ℕ} (S : OracleBlock k) : OracleBlock (k+36) :=
  seq (called S) (rename ConstraintSource.finish (lowEmbedding k))
noncomputable def calledTime (p : Polynomial ℕ) : Polynomial ℕ :=
  ConstraintSource.prepareTime+(NativeConstraintCall.time p).comp (X+ConstraintSource.prepareTime)+2
noncomputable def time (p : Polynomial ℕ) : Polynomial ℕ :=
  calledTime p+ConstraintSource.finishTime.comp (X+calledTime p)+2

lemma called_executes {k : ℕ} (S : OracleBlock k) (g : BitString→ℕ) (p : Polynomial ℕ)
    (hS : SolverSpec S g p) {n : ℕ} (G : MatrixGraph n) :
    ∃c,(called S).Executes g (Function.update (fun _ : Fin (k+37)=>[]) 0 (GraphInput.encode ⟨n,G⟩))
      (lifted (ConstraintSource.responseStore G)) c ∧
      c ≤ (calledTime p).eval (GraphInput.encode ⟨n,G⟩).length := by
  obtain ⟨a,ha,hab⟩:=ConstraintSource.prepare_executes g G
  let s:=SourceMetadata.outputStore (ConstraintSource.query G).encode (ConstraintSource.exponent G) n
    (forbidOccurrences (restoringIndependentProgram G).gates) (signOccurrences (restoringIndependentProgram G).gates)
  have hl:=lift_executes (k:=k) ConstraintSource.prepare g _ _ _ ha
  rw [lifted_initial] at hl
  obtain ⟨b,hb,hbb⟩:=NativeConstraintCall.program_executes S g p hS (ConstraintSource.query G) s rfl rfl
  have he : Function.update s 0 (RationalOracleEncoding.bits (ConstraintSource.query G).value)=
      ConstraintSource.responseStore G := by
    funext i
    simp only [Function.update_apply,s,SourceMetadata.outputStore,ConstraintSource.responseStore]
    by_cases h : i=0
    · subst i;rfl
    · have hv : i.val≠0 := by intro hv;exact h (Fin.ext hv)
      simp [h,hv]
  rw [he] at hb
  have hsize:=ha.stack_bound (ConstraintSource.input_bound (GraphInput.encode ⟨n,G⟩)) (0:Fin 36)
  change (ConstraintSource.query G).encode.length ≤ (GraphInput.encode ⟨n,G⟩).length+a at hsize
  have hm:=polynomial_nat_eval_mono (NativeConstraintCall.time p)
    (hsize.trans (Nat.add_le_add_left hab (GraphInput.encode ⟨n,G⟩).length))
  dsimp only at hm
  refine ⟨a+b+2,seq_executes _ _ g hl hb,?_⟩
  simp only [calledTime,eval_add,eval_comp,eval_X,eval_ofNat]
  omega

lemma program_executes {k : ℕ} (S : OracleBlock k) (g : BitString→ℕ) (p : Polynomial ℕ)
    (hS : SolverSpec S g p) (G : GraphInput) :
    ∃c,(program S).Executes g (Function.update (fun _ : Fin (k+37)=>[]) 0 G.encode)
      (Function.update (fun _ : Fin (k+37)=>[]) 0 (Computability.encodeNat G.2.independentCount)) c ∧
      c ≤ (time p).eval G.encode.length := by
  obtain ⟨n,G⟩:=G
  obtain ⟨c,hc,hb⟩:=called_executes S g p hS G
  have hin : ∀i : Fin (k+37),(Function.update (fun _ : Fin (k+37)=>[]) 0 (GraphInput.encode ⟨n,G⟩) i).length ≤
      (GraphInput.encode ⟨n,G⟩).length := by
    intro i;simp only [Function.update_apply];split_ifs <;> simp
  have hs:=hc.stack_bound hin
  have hsLow : ∀i : Fin 36,(ConstraintSource.responseStore G i).length ≤ (GraphInput.encode ⟨n,G⟩).length+c := by
    intro i
    have hi:=hs (lowEmbedding k i)
    change (lifted (ConstraintSource.responseStore G) (lowEmbedding k i)).length ≤
      (GraphInput.encode ⟨n,G⟩).length+c at hi
    simpa only [lifted,store_low] using hi
  have hsame : ConstraintSource.responseStore G=
      ConstraintSource.finishStore (pairBits (signedBits (ConstraintSource.numerator G)) (signedBits 1))
        (ConstraintSource.exponent G) n (forbidOccurrences (restoringIndependentProgram G).gates)
        (signOccurrences (restoringIndependentProgram G).gates) := by
    rw [ConstraintSource.responseStore,ConstraintSource.response_bits,ConstraintSource.initial_finishStore]
  obtain ⟨d,hd,hdb⟩:=ConstraintSource.finish_executes g (ConstraintSource.exponent G) n
    (forbidOccurrences (restoringIndependentProgram G).gates) (signOccurrences (restoringIndependentProgram G).gates)
    G.independentCount ((GraphInput.encode ⟨n,G⟩).length+c) (ConstraintSource.numerator G) rfl
    (by simpa only [←hsame] using hsLow)
  have hd':=lift_executes (k:=k) ConstraintSource.finish g _ _ _ hd
  rw [lifted_initial] at hd'
  have hc':=hc
  rw [ConstraintSource.responseStore,ConstraintSource.response_bits] at hc'
  have hm:=polynomial_nat_eval_mono ConstraintSource.finishTime
    (Nat.add_le_add_left hb (GraphInput.encode ⟨n,G⟩).length)
  dsimp only at hm
  refine ⟨c+d+2,seq_executes _ _ g hc' hd',?_⟩
  simp only [time,eval_add,eval_comp,eval_X,eval_ofNat]
  omega

theorem sharpPHard_of_solver {k : ℕ} (S : OracleBlock k) (g : BitString→ℕ) (p : Polynomial ℕ)
    (hS : SolverSpec S g p) : SharpPHard g := by
  apply sharpPHard_of_canonical_independent_block g (program S) (time p)
  intro G
  obtain ⟨c,hc,hb⟩:=program_executes S g p hS G
  exact ⟨_,c,hc,Function.update_self _ _ _,hb⟩
end HiddenCircuits.Circuit.Runtime.NativeConstraintSource
