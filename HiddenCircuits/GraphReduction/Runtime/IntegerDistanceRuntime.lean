import HiddenCircuits.GraphReduction.Runtime.IntegerDistanceDefs

namespace HiddenCircuits.GraphReduction.Runtime.IntegerDistance
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic RegisterMachine

theorem seed_executes (g : BitString → ℕ) (d x y : ℤ) :
    seed.Executes g (input d x y) (arithState (init d x y)) 16 := by
  convert seedFlags_executes [((4:Fin 17),true),(4,true),(5,false),(6,false),(7,false)] g (input d x y) using 1
  funext i;fin_cases i <;> first | rfl | (change signedBits (-1)=[true,true];decide +kernel)

theorem compute_executes (g : BitString → ℕ) (R : Fin 7 → ℤ) (B : ℕ) (hR:Bounded B R) (hv:Valid code R) :
    ∃c,compute.Executes g (arithState R) (arithState (evaluate code R)) c ∧c≤(straightTime code).eval B := by
  obtain ⟨c,hc,hb⟩:=compile_polynomial code g R B hR hv
  refine ⟨c,?_,hb⟩
  apply rename_executes_to _ arithMap g hc
  · clear hc;funext i;fin_cases i <;> rfl
  · clear hc;funext i;fin_cases i <;> rfl
  · clear hc;intro i hi
    fin_cases i <;> first | rfl | exact (hi 9 rfl).elim | exact (hi 10 rfl).elim | exact (hi 11 rfl).elim |
      exact (hi 12 rfl).elim | exact (hi 13 rfl).elim | exact (hi 14 rfl).elim | exact (hi 15 rfl).elim

theorem finish_executes (g : BitString → ℕ) (R : Fin 7 → ℤ) (C : ℕ) (hR:Bounded C R) (hC:1≤C) :
    ∃c,finish.Executes g (arithState R)
      (Function.update (fun _=>[]) 3 [!(negative (R 4)||negative (R 5))]) c ∧c≤10*C+60 := by
  let s0:=arithState R
  let s1:=Function.update (Function.update s0 (5:Fin 17) []) (8:Fin 17) [negative (R 4)]
  let s2:=Function.update (Function.update s1 (6:Fin 17) []) (9:Fin 17) [negative (R 5)]
  let s3:=Function.update (eraseStore [8,9] s2) (3:Fin 17) [!(negative (R 4)||negative (R 5))]
  have h1 : (SignFlag.on (5:Fin 17) 8 (by decide)).Executes g s0 s1 ((signedBits (R 4)).length+5) :=
    SignFlag.on_executes 5 8 (by decide) g s0 (R 4) rfl rfl
  have h2 : (SignFlag.on (6:Fin 17) 9 (by decide)).Executes g s1 s2 ((signedBits (R 5)).length+5) :=
    SignFlag.on_executes 6 9 (by decide) g s1 (R 5) rfl rfl
  have h3 : decideSigns.Executes g s2 s3 8 := by
    have h:=Complexity.GraphVerifier.Runtime.decision_executes (3:Fin 17) [8,9] (by decide) (by decide)
      (fun bs=> !(bs[0]?.getD true ||bs[1]?.getD true)) (fun i=>if i.val=8 then negative (R 4) else negative (R 5)) g s2 (by
        intro i hi;simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl <;> rfl)
    exact h
  have hbound : ∀i,(s3 i).length≤C := by
    intro i;fin_cases i <;> simp [s3,s2,s1,s0,arithState,state,eraseStore]
    all_goals first | exact hR 0 | exact hR 1 | exact hR 2 | exact hR 3 | exact hR 6 | exact hC
  obtain ⟨c,hc,hb⟩:=clearList_executes g [(0:Fin 17),1,2,4,7] s3 C hbound
  have he : eraseStore [(0:Fin 17),1,2,4,7] s3=Function.update (fun _=>[]) 3 [!(negative (R 4)||negative (R 5))] := by
    funext i;fin_cases i <;> rfl
  rw [he] at hc
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 hc)),?_⟩
  have h4:=hR 4;have h5:=hR 5
  simp only [List.length_cons,List.length_nil] at hb
  omega

theorem program_executes (g : BitString → ℕ) (d x y : ℤ) (B : ℕ)
    (hd:(signedBits d).length≤B) (hx:(signedBits x).length≤B) (hy:(signedBits y).length≤B) (hB:2≤B) :
    ∃c,program.Executes g (input d x y) (Function.update (fun _=>[]) 3 [answer d x y]) c ∧c≤time.eval B := by
  have hb:=init_bounded d x y B hd hx hy hB
  obtain ⟨a,ha,hba⟩:=compute_executes g (init d x y) B hb (code_valid d x y)
  obtain ⟨c,hc,hbc⟩:=finish_executes g (evaluate code (init d x y)) (resultBound B) (result_bounded d x y B hb)
    (by unfold resultBound;omega)
  have he : (!(negative (evaluate code (init d x y) 4)||negative (evaluate code (init d x y) 5)))=answer d x y := by
    rw [code_value]
    apply Bool.eq_iff_iff.mpr
    simp [negative,answer]
    omega
  rw [he] at hc
  refine ⟨_,seq_executes _ _ g (seed_executes g d x y) (seq_executes _ _ g ha hc),?_⟩
  simp only [time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  unfold resultBound at hbc
  omega
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (seedFlags_queryFree _)
  (seq_queryFree _ _ (rename_queryFree _ _ (compile_queryFree _))
    (seq_queryFree _ _ (SignFlag.on_queryFree _ _ _) (seq_queryFree _ _ (SignFlag.on_queryFree _ _ _)
      (seq_queryFree _ _ (Complexity.GraphVerifier.Runtime.decision_queryFree _ _ _) (clearList_queryFree _)))))
end HiddenCircuits.GraphReduction.Runtime.IntegerDistance
