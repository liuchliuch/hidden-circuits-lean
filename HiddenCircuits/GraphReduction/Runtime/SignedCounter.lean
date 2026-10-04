import HiddenCircuits.GraphReduction.Runtime.SignedScanDefs

/-! A two-bit sign selector consumes its input and performs a real
canonical signed addition with the literal +1 or -1 register. -/
namespace HiddenCircuits.GraphReduction.Runtime.SignedCounter
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic RegisterMachine
open SignedScan

def instruction (negative : Bool) : Instruction :=
  ⟨.add,2,2,if negative then 6 else 5⟩
noncomputable def add (negative : Bool) : OracleBlock 95 :=
  rename (compile [instruction negative]) arithmeticMap
noncomputable def program : OracleBlock 95 :=
  branchPop 3 skip (branchPop 3 skip skip (add true)) (seq (clear 3) (add false))
noncomputable def timePolynomial : Polynomial ℕ :=
  straightTime [instruction false]+straightTime [instruction true]+10

lemma add_executes (negative : Bool) (g : BitString → ℕ)
    (n i j : ℕ) (out inner outer : BitString) (params : Store 95)
    (R : Fin 7 → ℤ) (C : ℕ) (hR : Bounded C R) (h1 : R 5=1) (hn : R 6=-1) :
    ∃ t, (add negative).Executes g (state n i j [] out inner outer params R)
      (state n i j [] out inner outer params
        (Function.update R 2 (R 2+(if negative then -1 else 1)))) t ∧
      t≤(straightTime [instruction negative]).eval C := by
  obtain ⟨t,ht,hb⟩ := compile_polynomial [instruction negative] g R C hR (by
    simp [Valid,instruction,Operation.Valid])
  have he : evaluate [instruction negative] R=
      Function.update R 2 (R 2+(if negative then -1 else 1)) := by
    cases negative <;> simp [evaluate,Instruction.eval,instruction,Operation.eval,h1,hn]
  rw [he] at ht
  refine ⟨t,?_,hb⟩
  apply rename_executes_to _ arithmeticMap g ht
  · funext q; exact SignedScan.state_arithmetic _ _ _ _ _ _ _ _ _ q
  · funext q; exact SignedScan.state_arithmetic _ _ _ _ _ _ _ _ _ q
  · intro q hq
    have hlt : ¬80≤q.val := by
      intro hh
      exact hq ⟨q.val-80,by omega⟩ (Fin.ext (by simp [arithmeticMap];omega))
    simp only [state,hlt,↓reduceDIte]

 theorem program_executes (g : BitString → ℕ) (n i j : ℕ) (bits : Bool × Bool)
    (out inner outer : BitString) (params : Store 95) (R : Fin 7 → ℤ) (C : ℕ)
    (hR : Bounded C R) (h1 : R 5=1) (hn : R 6=-1) :
    ∃ t, program.Executes g (state n i j [bits.1,bits.2] out inner outer params R)
      (state n i j [] out inner outer params (Function.update R 2 (R 2+value bits))) t ∧
      t≤timePolynomial.eval C := by
  rcases bits with ⟨a,b⟩
  cases a with
  | false =>
    cases b with
    | false =>
      have he : Function.update R 2 (R 2+value (false,false))=R := by
        simp [value]
      rw [he]
      refine ⟨5,branchPop_false _ _ _ _ g rfl ?_,?_⟩
      · rw [update_bits]
        apply branchPop_false _ _ _ _ g rfl
        rw [update_bits]
        exact skip_executes g _
      · simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_ofNat]; omega
    | true =>
      obtain ⟨t,ht,hb⟩ := add_executes true g n i j out inner outer params R C hR h1 hn
      refine ⟨t+4,?_,?_⟩
      · convert branchPop_false (3 : Fin 96) skip (branchPop 3 skip skip (add true))
          (seq (clear 3) (add false)) g (s:=state n i j [false,true] out inner outer params R) rfl
          (by rw [update_bits]; apply branchPop_true _ _ _ _ g rfl; rw [update_bits]; exact ht) using 1
      · simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_ofNat]; omega
  | true =>
    obtain ⟨t,ht,hb⟩ := add_executes false g n i j out inner outer params R C hR h1 hn
    have hc : (clear (3 : Fin 96)).Executes g (state n i j [b] out inner outer params R)
        (state n i j [] out inner outer params R) 2 := by
      simpa only [show state n i j [b] out inner outer params R 3=[b] from rfl,
        List.length_singleton,update_bits] using clear_executes g (3 : Fin 96) (state n i j [b] out inner outer params R)
    refine ⟨t+6,?_,?_⟩
    · convert branchPop_true (3 : Fin 96) skip (branchPop 3 skip skip (add true))
        (seq (clear 3) (add false)) g (s:=state n i j [true,b] out inner outer params R) rfl
        (by rw [update_bits]; exact seq_executes _ _ g hc ht) using 1 <;> simp [value,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
    · simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_ofNat]; omega

lemma program_queryFree : program.QueryFree :=
  branchPop_queryFree _ _ _ _ skip_queryFree
    (branchPop_queryFree _ _ _ _ skip_queryFree skip_queryFree (rename_queryFree _ _ (compile_queryFree _)))
    (seq_queryFree _ _ (clear_queryFree _) (rename_queryFree _ _ (compile_queryFree _)))

end HiddenCircuits.GraphReduction.Runtime.SignedCounter
