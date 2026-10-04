import HiddenCircuits.DH.Runtime.PairCheckLoop

/-! Literal complete pendant/twin testing with preserved ordinary input stores. -/
namespace HiddenCircuits.DH.Runtime.PairCheck.TestRuntime
open Complexity Complexity.OracleBlock

def store (n u v : ℕ) (payload marks output : BitString) : Store 22 :=
  state n u v 0 payload marks output [] (flags [] [] [] [] [] [] [] [] [] [] [])
noncomputable def header : OracleBlock 22 := seq readU (seq readV
  (seq compareUV (seq readVU (push 8 true))))
def finalDecision (mode : Bool) : List Bool → Bool
  | [a,au,av,eq,edge] => au && av && !eq && (mode || edge) && a
  | _ => false
noncomputable def finish (mode : Bool) : OracleBlock 22 :=
  GraphVerifier.Runtime.decision 5 [8,9,10,11,12] (finalDecision mode)
noncomputable def program (mode : Bool) : OracleBlock 22 := seq header
  (seq (copyOn 0 7 19 (by decide) (by decide) (by decide))
    (seq (loop mode) (seq (clear 6) (finish mode))))

lemma header_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (alive : Vector Bool n) (u v : Fin n) :
    ∃t, header.Executes g (store n u.val v.val G.bits (liveBits alive) [])
      (state n u.val v.val 0 G.bits (liveBits alive) [] []
        (flags [true] [alive[u.val]] [alive[v.val]] [decide (u=v)] [G.edge v u] [] [] [] [] [] [])) t ∧
      t≤410*(n+1)^2 := by
  obtain ⟨t1,ht1,hb1⟩ := readU_executes g G alive u v 0 [] [] (flags [] [] [] [] [] [] [] [] [] [] []) rfl
  have h1 : readU.Executes g (state n u.val v.val 0 G.bits (liveBits alive) [] []
        (flags [] [] [] [] [] [] [] [] [] [] [])) (state n u.val v.val 0 G.bits (liveBits alive) [] []
        (flags [] [alive[u.val]] [] [] [] [] [] [] [] [] [])) t1 := by
    convert ht1 using 1
  obtain ⟨t2,ht2,hb2⟩ := readV_executes g G alive u v 0 [] [] (flags [] [alive[u.val]] [] [] [] [] [] [] [] [] []) rfl
  have h2 : readV.Executes g (state n u.val v.val 0 G.bits (liveBits alive) [] []
        (flags [] [alive[u.val]] [] [] [] [] [] [] [] [] [])) (state n u.val v.val 0 G.bits (liveBits alive) [] []
        (flags [] [alive[u.val]] [alive[v.val]] [] [] [] [] [] [] [] [])) t2 := by
    convert ht2 using 1
  obtain ⟨t3,ht3,hb3⟩ := compareUV_executes g G alive u v 0 [] [] (flags [] [alive[u.val]] [alive[v.val]] [] [] [] [] [] [] [] []) rfl
  have h3 : compareUV.Executes g (state n u.val v.val 0 G.bits (liveBits alive) [] []
        (flags [] [alive[u.val]] [alive[v.val]] [] [] [] [] [] [] [] [])) (state n u.val v.val 0 G.bits (liveBits alive) [] []
        (flags [] [alive[u.val]] [alive[v.val]] [decide (u=v)] [] [] [] [] [] [] [])) t3 := by
    convert ht3 using 1
  obtain ⟨t4,ht4,hb4⟩ := readVU_executes g G alive u v 0 [] [] (flags [] [alive[u.val]] [alive[v.val]] [decide (u=v)] [] [] [] [] [] [] []) rfl
  have h4 : readVU.Executes g (state n u.val v.val 0 G.bits (liveBits alive) [] []
        (flags [] [alive[u.val]] [alive[v.val]] [decide (u=v)] [] [] [] [] [] [] [])) (state n u.val v.val 0 G.bits (liveBits alive) [] []
        (flags [] [alive[u.val]] [alive[v.val]] [decide (u=v)] [G.edge v u] [] [] [] [] [] [])) t4 := by
    convert ht4 using 1
  have h5 : (push (8 : Fin 23) true).Executes g (state n u.val v.val 0 G.bits (liveBits alive) [] []
        (flags [] [alive[u.val]] [alive[v.val]] [decide (u=v)] [G.edge v u] [] [] [] [] [] [])) (state n u.val v.val 0 G.bits (liveBits alive) [] []
        (flags [true] [alive[u.val]] [alive[v.val]] [decide (u=v)] [G.edge v u] [] [] [] [] [] [])) 1 := by
    convert push_executes g (8 : Fin 23) true (state n u.val v.val 0 G.bits (liveBits alive) [] []
        (flags [] [alive[u.val]] [alive[v.val]] [decide (u=v)] [G.edge v u] [] [] [] [] [] [])) using 1
    funext i;fin_cases i <;> simp [state,flags]
  refine ⟨t1+(t2+(t3+(t4+1+2)+2)+2)+2,
    seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 (seq_executes _ _ g h4 h5))),?_⟩
  have hN : 1≤(n+1)^2 := Nat.one_le_pow 2 (n+1) (by omega)
  omega

lemma program_executes (mode : Bool) (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (alive : Vector Bool n) (u v : Fin n) :
    ∃t, (program mode).Executes g (store n u.val v.val G.bits (liveBits alive) [])
      (store n u.val v.val G.bits (liveBits alive) [test mode G alive u v]) t ∧
      t≤1000*(n+1)^3 := by
  let f := flags [true] [alive[u.val]] [alive[v.val]] [decide (u=v)] [G.edge v u] [] [] [] [] [] []
  let a := cellsFrom (cell mode G alive u v) 0 n
  let f' := flags [a] [alive[u.val]] [alive[v.val]] [decide (u=v)] [G.edge v u] [] [] [] [] [] []
  obtain ⟨th,hh,hbh⟩ := header_executes g G alive u v
  have hc : (copyOn (0 : Fin 23) 7 19 (by decide) (by decide) (by decide)).Executes g
      (state n u.val v.val 0 G.bits (liveBits alive) [] [] f)
      (state n u.val v.val 0 G.bits (liveBits alive) [] (List.replicate n true) f) (5*n+2) := by
    convert copyOn_executes g (0 : Fin 23) 7 19 (by decide) (by decide) (by decide)
      (state n u.val v.val 0 G.bits (liveBits alive) [] [] f) rfl using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state]
  obtain ⟨tl,hl,hbl⟩ := loop_execution mode g G alive u v 0 n (by omega)
    [] [alive[u.val]] [alive[v.val]] [decide (u=v)] [G.edge v u] true
  have hl' : (loop mode).Executes g
      (state n u.val v.val 0 G.bits (liveBits alive) [] (List.replicate n true) f)
      (state n u.val v.val n G.bits (liveBits alive) [] [] f') tl := by
    simpa only [Nat.zero_add,Bool.true_and] using whilePop_executes _ _ _ g hl
  have hclear : (clear (6 : Fin 23)).Executes g
      (state n u.val v.val n G.bits (liveBits alive) [] [] f')
      (state n u.val v.val 0 G.bits (liveBits alive) [] [] f') (n+1) := by
    convert clear_executes g (6 : Fin 23) (state n u.val v.val n G.bits (liveBits alive) [] [] f') using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state]
  let bits : Fin 23 → Bool := ![false,false,false,false,false,false,false,false,
    a,alive[u.val],alive[v.val],decide (u=v),G.edge v u,false,false,false,false,false,false,false,false,false,false]
  have hf : (finish mode).Executes g (state n u.val v.val 0 G.bits (liveBits alive) [] [] f')
      (store n u.val v.val G.bits (liveBits alive) [test mode G alive u v]) 14 := by
    have ht := GraphVerifier.Runtime.decision_executes (5 : Fin 23) [8,9,10,11,12]
      (by decide) (by decide) (finalDecision mode) bits g
      (state n u.val v.val 0 G.bits (liveBits alive) [] [] f')
      (by intro i hi;fin_cases i <;> simp [state,f',flags,bits] at *)
    convert ht using 1
    funext i;fin_cases i <;> simp [store,state,f',flags,bits,eraseStore,finalDecision,test,a]
  refine ⟨th+((5*n+2)+(tl+((n+1)+14+2)+2)+2)+2,
    seq_executes _ _ g hh (seq_executes _ _ g hc (seq_executes _ _ g hl' (seq_executes _ _ g hclear hf))),?_⟩
  nlinarith

lemma header_queryFree : header.QueryFree := seq_queryFree _ _ readU_queryFree
  (seq_queryFree _ _ readV_queryFree (seq_queryFree _ _ compareUV_queryFree
    (seq_queryFree _ _ readVU_queryFree (push_queryFree _ _))))
lemma program_queryFree (mode : Bool) : (program mode).QueryFree := seq_queryFree _ _ header_queryFree
  (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (loop_queryFree mode)
    (seq_queryFree _ _ (clear_queryFree _) (GraphVerifier.Runtime.decision_queryFree _ _ _))))

end HiddenCircuits.DH.Runtime.PairCheck.TestRuntime
