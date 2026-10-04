import HiddenCircuits.Circuit.Runtime.ProjectionStreamPrepare

namespace HiddenCircuits.Circuit.Runtime.ProjectionStream
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic LetterEmitter

noncomputable def scan : OracleBlock 10 := seq (copyOn 0 4 7 (by decide) (by decide) (by decide))
  (seq filterLoop (clear 3))
def scanTime (n : ℕ) : ℕ := n*(3000*(4*n+1)+2)+9*n+8

theorem scan_executes (oracle : BitString → ℕ) (n r : ℕ) (out exponent : BitString) :
    ∃t, scan.Executes oracle (store n 0 0 r out exponent)
      (store n 0 0 r ((filterStream 0 n).reverse++out) (List.replicate (6*n) true++exponent)) t ∧ t≤scanTime n := by
  have hc : (copyOn (0:Fin 11) 4 7 (by decide) (by decide) (by decide)).Executes oracle
      (store n 0 0 r out exponent) (store n 0 n r out exponent) (5*n+2) := by
    convert copyOn_executes oracle (0:Fin 11) 4 7 (by decide) (by decide) (by decide) (store n 0 0 r out exponent) rfl using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  obtain ⟨a,ha,hab⟩ := filterLoop_executes oracle n n 0 r out exponent
  simp only [Nat.zero_add] at ha hab
  have hclear : (clear (3:Fin 11)).Executes oracle
      (store n (4*n) 0 r ((filterStream 0 n).reverse++out) (List.replicate (6*n) true++exponent))
      (store n 0 0 r ((filterStream 0 n).reverse++out) (List.replicate (6*n) true++exponent)) (4*n+1) := by
    convert clear_executes oracle (3:Fin 11)
      (store n (4*n) 0 r ((filterStream 0 n).reverse++out) (List.replicate (6*n) true++exponent)) using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  refine ⟨_,seq_executes _ _ oracle hc (seq_executes _ _ oracle ha hclear),?_⟩
  unfold scanTime
  omega

noncomputable def projectionLoop : OracleBlock 10 := whilePop 5 scan scan

theorem projectionLoop_execution (oracle : BitString → ℕ) (r n : ℕ) (out exponent : BitString) :
    ∃t, WhileExecution (5:Fin 11) scan scan oracle (store n 0 0 r out exponent)
      (store n 0 0 0 ((List.replicate r (filterStream 0 n)).flatten.reverse++out)
        (List.replicate (6*n*r) true++exponent)) t ∧ t≤r*(scanTime n+2)+1 := by
  induction r generalizing out exponent with
  | zero =>
    refine ⟨1,?_,by omega⟩
    simpa using (WhileExecution.empty (stack:=(5:Fin 11)) (B:=scan) (C:=scan) (g:=oracle) (store n 0 0 0 out exponent) rfl)
  | succ r ih =>
    obtain ⟨a,ha,hab⟩ := scan_executes oracle n r out exponent
    have hs : Function.update (store n 0 0 (r+1) out exponent) (5:Fin 11) (List.replicate r true)=store n 0 0 r out exponent := by
      funext i;fin_cases i <;> simp [store]
    rw [←hs] at ha
    obtain ⟨b,hb,hbb⟩ := ih ((filterStream 0 n).reverse++out) (List.replicate (6*n) true++exponent)
    have hh := WhileExecution.one (stack:=(5:Fin 11))
      (show store n 0 0 (r+1) out exponent 5=true::List.replicate r true from rfl) ha hb
    refine ⟨1+a+1+b,?_,?_⟩
    · convert hh using 1
      simp only [List.replicate_succ,List.flatten_cons,List.reverse_append,←List.append_assoc,←List.replicate_add,Nat.mul_add,Nat.mul_one]
    · nlinarith

theorem projectionLoop_executes (oracle : BitString → ℕ) (r n : ℕ) (out exponent : BitString) :
    ∃t, projectionLoop.Executes oracle (store n 0 0 r out exponent)
      (store n 0 0 0 ((List.replicate r (filterStream 0 n)).flatten.reverse++out)
        (List.replicate (6*n*r) true++exponent)) t ∧ t≤r*(scanTime n+2)+1 := by
  obtain ⟨t,ht,hb⟩ := projectionLoop_execution oracle r n out exponent
  exact ⟨t,whilePop_executes _ _ _ _ ht,hb⟩
theorem scan_queryFree : scan.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ filterLoop_queryFree (clear_queryFree _))
theorem projectionLoop_queryFree : projectionLoop.QueryFree := whilePop_queryFree _ _ _ scan_queryFree scan_queryFree
end HiddenCircuits.Circuit.Runtime.ProjectionStream
