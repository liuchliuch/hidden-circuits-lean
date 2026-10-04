import HiddenCircuits.GraphReduction.Runtime.SignedCounter

/-! A literal unary-clocked scan invokes a verified callback for
all descriptor indices, updates a signed coordinate, and cleans the loop ports. -/
namespace HiddenCircuits.GraphReduction.Runtime.SignedScan
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic RegisterMachine

noncomputable def body (B : OracleBlock 95) : OracleBlock 95 :=
  seq B (seq SignedCounter.program (push 2 true))
noncomputable def loop (B : OracleBlock 95) : OracleBlock 95 := whilePop 5 (body B) (body B)
noncomputable def copyInner : OracleBlock 95 := copyOn 0 5 7 (by decide) (by decide) (by decide)
noncomputable def program (B : OracleBlock 95) : OracleBlock 95 :=
  seq copyInner (seq (loop B) (clear 2))
noncomputable def bound (n T C : ℕ) : ℕ :=
  n*(T+SignedCounter.timePolynomial.eval (SignedCounter.counterBound C n)+7)+6*n+8

 theorem body_executes (B : OracleBlock 95) (edge : ℕ → ℕ → Bool × Bool)
    (n T : ℕ) (params : Store 95)
    (hB : ∀ g i j out inner outer R, i<n → j<n →
      ∃ t, B.Executes g (state n i j [] out inner outer params R)
        (state n i j [(edge i j).1,(edge i j).2] out inner outer params R) t ∧ t≤T)
    (g : BitString → ℕ) (i j : ℕ) (out inner outer : BitString) (R : Fin 7 → ℤ) (C : ℕ)
    (hR : Bounded C R) (h1 : R 5=1) (hn : R 6=-1) (hi:i<n) (hj:j<n) :
    ∃ t, (body B).Executes g (state n i j [] out inner outer params R)
      (state n i (j+1) [] out inner outer params
        (Function.update R 2 (R 2+SignedCounter.value (edge i j)))) t ∧
      t≤T+SignedCounter.timePolynomial.eval C+5 := by
  obtain ⟨a,ha,hba⟩ := hB g i j out inner outer R hi hj
  obtain ⟨b,hb,hbb⟩ := SignedCounter.program_executes g n i j (edge i j) out inner outer params R C hR h1 hn
  have hp : (push (2 : Fin 96) true).Executes g
      (state n i j [] out inner outer params (Function.update R 2 (R 2+SignedCounter.value (edge i j))))
      (state n i (j+1) [] out inner outer params (Function.update R 2 (R 2+SignedCounter.value (edge i j)))) 1 := by
    simpa only [show state n i j [] out inner outer params (Function.update R 2 (R 2+SignedCounter.value (edge i j))) 2=List.replicate j true from rfl,
      update_column] using push_executes g (2 : Fin 96) true
        (state n i j [] out inner outer params (Function.update R 2 (R 2+SignedCounter.value (edge i j))))
  exact ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb hp),by omega⟩

 theorem loop_executes (B : OracleBlock 95) (edge : ℕ → ℕ → Bool × Bool)
    (n T : ℕ) (params : Store 95)
    (hB : ∀ g i j out inner outer R, i<n → j<n →
      ∃ t, B.Executes g (state n i j [] out inner outer params R)
        (state n i j [(edge i j).1,(edge i j).2] out inner outer params R) t ∧ t≤T)
    (g : BitString → ℕ) (i j m : ℕ) (out outer : BitString) (R : Fin 7 → ℤ) (C : ℕ)
    (hR : Bounded C R) (h1 : R 5=1) (hn : R 6=-1) (hi:i<n) (hjm:j+m≤n)
    (d : ℤ) (hd:d.natAbs+m≤n) :
    ∃ t, WhileExecution 5 (body B) (body B) g
      (state n i j [] out (List.replicate m true) outer params (Function.update R 2 (R 2+d)))
      (state n i (j+m) [] out [] outer params (Function.update R 2 (R 2+(d+total edge i j m)))) t ∧
      t≤m*(T+SignedCounter.timePolynomial.eval (SignedCounter.counterBound C n)+7)+1 := by
  induction m generalizing j d with
  | zero =>
    refine ⟨1,?_,by simp⟩
    simpa only [Nat.add_zero,total,add_zero] using
      (WhileExecution.empty (stack:=(5 : Fin 96)) (B:=body B) (C:=body B) (g:=g)
        (state n i j [] out [] outer params (Function.update R 2 (R 2+d))) rfl)
  | succ m ih =>
    have hd0 : d.natAbs≤n := by omega
    have hcurr := SignedCounter.bounded_counter R C n d hR hd0
    obtain ⟨a,ha,hba⟩ := body_executes B edge n T params hB g i j out (List.replicate m true) outer
      (Function.update R 2 (R 2+d)) (SignedCounter.counterBound C n) hcurr
      (by simpa using h1) (by simpa using hn) hi (by omega)
    have he : Function.update (Function.update R 2 (R 2+d)) 2
        ((Function.update R 2 (R 2+d)) 2+SignedCounter.value (edge i j))=
        Function.update R 2 (R 2+(d+SignedCounter.value (edge i j))) := by
      simp only [Function.update_self,Function.update_idem,add_assoc]
    rw [he] at ha
    have hnext : (d+SignedCounter.value (edge i j)).natAbs+m≤n := by
      have hval := SignedCounter.value_abs (edge i j)
      have hsum := Int.natAbs_add_le d (SignedCounter.value (edge i j))
      omega
    obtain ⟨b,hb,hbb⟩ := ih (j+1) (by omega) (d+SignedCounter.value (edge i j)) hnext
    have hp : state n i j [] out (List.replicate (m+1) true) outer params (Function.update R 2 (R 2+d)) 5=
        true::List.replicate m true := by simp [state,MatrixEmitter.store,MatrixEmitter.port,List.replicate_succ]
    have hh := WhileExecution.one (stack:=(5 : Fin 96)) (B:=body B) (C:=body B) (g:=g) hp
      (by rw [update_inner];exact ha) hb
    refine ⟨1+a+1+b,?_,?_⟩
    · simpa only [total,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,add_assoc] using hh
    · nlinarith

 theorem copyInner_executes (g : BitString → ℕ) (n i j : ℕ) (out outer : BitString)
    (params : Store 95) (R : Fin 7 → ℤ) :
    copyInner.Executes g (state n i j [] out [] outer params R)
      (state n i j [] out (List.replicate n true) outer params R) (5*n+2) := by
  have h := copyOn_executes g (0 : Fin 96) 5 7 (by decide) (by decide) (by decide)
    (state n i j [] out [] outer params R) rfl
  simpa only [show state n i j [] out [] outer params R 0=List.replicate n true from rfl,
    show state n i j [] out [] outer params R 5=[] from rfl,
    List.append_nil,List.length_replicate,update_inner] using h

 theorem program_executes (B : OracleBlock 95) (edge : ℕ → ℕ → Bool × Bool)
    (n T : ℕ) (params : Store 95)
    (hB : ∀ g i j out inner outer R, i<n → j<n →
      ∃ t, B.Executes g (state n i j [] out inner outer params R)
        (state n i j [(edge i j).1,(edge i j).2] out inner outer params R) t ∧ t≤T)
    (g : BitString → ℕ) (i : ℕ) (out outer : BitString) (R : Fin 7 → ℤ) (C : ℕ)
    (hR : Bounded C R) (h1 : R 5=1) (hn : R 6=-1) (hi:i<n) :
    ∃ t, (program B).Executes g (state n i 0 [] out [] outer params R)
      (state n i 0 [] out [] outer params (Function.update R 2 (R 2+total edge i 0 n))) t ∧
      t≤bound n T C := by
  obtain ⟨a,ha,hba⟩ := loop_executes B edge n T params hB g i 0 n out outer R C hR h1 hn hi (by omega) 0 (by simp)
  simp only [Int.natAbs_zero,add_zero,zero_add,Nat.zero_add,Function.update_eq_self] at ha
  have hl := whilePop_executes _ _ _ g ha
  have hc : (clear (2 : Fin 96)).Executes g
      (state n i n [] out [] outer params (Function.update R 2 (R 2+total edge i 0 n)))
      (state n i 0 [] out [] outer params (Function.update R 2 (R 2+total edge i 0 n))) (n+1) := by
    simpa only [show state n i n [] out [] outer params (Function.update R 2 (R 2+total edge i 0 n)) 2=List.replicate n true from rfl,
      List.length_replicate,clear_column] using clear_executes g (2 : Fin 96)
        (state n i n [] out [] outer params (Function.update R 2 (R 2+total edge i 0 n)))
  refine ⟨_,seq_executes _ _ g (copyInner_executes g n i 0 out outer params R)
      (seq_executes _ _ g hl hc),?_⟩
  unfold bound
  omega

lemma program_queryFree (B : OracleBlock 95) (hB:B.QueryFree) : (program B).QueryFree := by
  have hb : (body B).QueryFree := seq_queryFree _ _ hB
    (seq_queryFree _ _ SignedCounter.program_queryFree (push_queryFree _ _))
  exact seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (whilePop_queryFree _ _ _ hb hb) (clear_queryFree _))

end HiddenCircuits.GraphReduction.Runtime.SignedScan
