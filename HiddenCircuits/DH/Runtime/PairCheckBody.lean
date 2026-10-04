import HiddenCircuits.DH.Runtime.PairCheckReads

/-! One literal scan-cell operation for twin or pendant testing. -/
namespace HiddenCircuits.DH.Runtime.PairCheck.TestRuntime
open Complexity Complexity.OracleBlock

/-- A fixed six-bit truth table, compiled to branches and pushes. -/
def cellDecision (mode : Bool) : List Bool → Bool
  | [a,l,eu,ev,vx,ux] => a && (!l || if mode then eu || ev || (vx == ux) else !vx || eu)
  | _ => false
noncomputable def decideCell (mode : Bool) : OracleBlock 22 :=
  GraphVerifier.Runtime.decision 18 [8,13,14,15,16,17] (cellDecision mode)
noncomputable def body (mode : Bool) : OracleBlock 22 := seq readX (seq compareXU
  (seq compareXV (seq readVX (seq readUX (seq (decideCell mode)
    (seq (reverseOn 18 8 (by decide)) (push 6 true)))))))

lemma body_executes (mode : Bool) (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (alive : Vector Bool n) (u v x : Fin n) (output clock au av eq edge : BitString) (a : Bool) :
    ∃t, (body mode).Executes g
      (state n u.val v.val x.val G.bits (liveBits alive) output clock
        (flags [a] au av eq edge [] [] [] [] [] []))
      (state n u.val v.val (x.val+1) G.bits (liveBits alive) output clock
        (flags [a && cell mode G alive u v x] au av eq edge [] [] [] [] [] [])) t ∧
      t≤550*(n+1)^2 := by
  obtain ⟨t1,ht1,hb1⟩ := readX_executes g G alive u v x output clock (flags [a] au av eq edge [] [] [] [] [] []) rfl
  have h1 : readX.Executes g (state n u.val v.val x.val G.bits (liveBits alive) output clock
        (flags [a] au av eq edge [] [] [] [] [] []))
      (state n u.val v.val x.val G.bits (liveBits alive) output clock
        (flags [a] au av eq edge [alive[x.val]] [] [] [] [] [])) t1 := by
    convert ht1 using 1
  obtain ⟨t2,ht2,hb2⟩ := compareXU_executes g G alive u v x output clock (flags [a] au av eq edge [alive[x.val]] [] [] [] [] []) rfl
  have h2 : compareXU.Executes g (state n u.val v.val x.val G.bits (liveBits alive) output clock
        (flags [a] au av eq edge [alive[x.val]] [] [] [] [] []))
      (state n u.val v.val x.val G.bits (liveBits alive) output clock
        (flags [a] au av eq edge [alive[x.val]] [decide (x=u)] [] [] [] [])) t2 := by
    convert ht2 using 1
  obtain ⟨t3,ht3,hb3⟩ := compareXV_executes g G alive u v x output clock (flags [a] au av eq edge [alive[x.val]] [decide (x=u)] [] [] [] []) rfl
  have h3 : compareXV.Executes g (state n u.val v.val x.val G.bits (liveBits alive) output clock
        (flags [a] au av eq edge [alive[x.val]] [decide (x=u)] [] [] [] []))
      (state n u.val v.val x.val G.bits (liveBits alive) output clock
        (flags [a] au av eq edge [alive[x.val]] [decide (x=u)] [decide (x=v)] [] [] [])) t3 := by
    convert ht3 using 1
  obtain ⟨t4,ht4,hb4⟩ := readVX_executes g G alive u v x output clock (flags [a] au av eq edge [alive[x.val]] [decide (x=u)] [decide (x=v)] [] [] []) rfl
  have h4 : readVX.Executes g (state n u.val v.val x.val G.bits (liveBits alive) output clock
        (flags [a] au av eq edge [alive[x.val]] [decide (x=u)] [decide (x=v)] [] [] []))
      (state n u.val v.val x.val G.bits (liveBits alive) output clock
        (flags [a] au av eq edge [alive[x.val]] [decide (x=u)] [decide (x=v)] [G.edge v x] [] [])) t4 := by
    convert ht4 using 1
  obtain ⟨t5,ht5,hb5⟩ := readUX_executes g G alive u v x output clock (flags [a] au av eq edge [alive[x.val]] [decide (x=u)] [decide (x=v)] [G.edge v x] [] []) rfl
  have h5 : readUX.Executes g (state n u.val v.val x.val G.bits (liveBits alive) output clock
        (flags [a] au av eq edge [alive[x.val]] [decide (x=u)] [decide (x=v)] [G.edge v x] [] []))
      (state n u.val v.val x.val G.bits (liveBits alive) output clock
        (flags [a] au av eq edge [alive[x.val]] [decide (x=u)] [decide (x=v)] [G.edge v x] [G.edge u x] [])) t5 := by
    convert ht5 using 1
  let bits : Fin 23 → Bool := ![false,false,false,false,false,false,false,false,a,false,false,false,false,alive[x.val],decide (x=u),decide (x=v),G.edge v x,G.edge u x,false,false,false,false,false]
  have h6 : (decideCell mode).Executes g (state n u.val v.val x.val G.bits (liveBits alive) output clock
        (flags [a] au av eq edge [alive[x.val]] [decide (x=u)] [decide (x=v)] [G.edge v x] [G.edge u x] []))
      (state n u.val v.val x.val G.bits (liveBits alive) output clock
        (flags [] au av eq edge [] [] [] [] [] [a && cell mode G alive u v x])) 16 := by
    have ht := GraphVerifier.Runtime.decision_executes (18 : Fin 23) [8,13,14,15,16,17]
      (by decide) (by decide) (cellDecision mode) bits g (state n u.val v.val x.val G.bits (liveBits alive) output clock
        (flags [a] au av eq edge [alive[x.val]] [decide (x=u)] [decide (x=v)] [G.edge v x] [G.edge u x] []))
      (by intro i hi;fin_cases i <;> simp [state,flags,bits] at *)
    convert ht using 1
    funext i;fin_cases i <;> simp [state,flags,bits,eraseStore,cellDecision,cell]
  have h7 : (reverseOn (18 : Fin 23) 8 (by decide)).Executes g
      (state n u.val v.val x.val G.bits (liveBits alive) output clock
        (flags [] au av eq edge [] [] [] [] [] [a && cell mode G alive u v x]))
      (state n u.val v.val x.val G.bits (liveBits alive) output clock
        (flags [a && cell mode G alive u v x] au av eq edge [] [] [] [] [] [])) 3 := by
    convert reverseOn_executes g (18 : Fin 23) 8 (by decide)
      (state n u.val v.val x.val G.bits (liveBits alive) output clock
        (flags [] au av eq edge [] [] [] [] [] [a && cell mode G alive u v x])) using 1
    funext i;fin_cases i <;> simp [state,flags]
  have h8 : (push (6 : Fin 23) true).Executes g
      (state n u.val v.val x.val G.bits (liveBits alive) output clock
        (flags [a && cell mode G alive u v x] au av eq edge [] [] [] [] [] []))
      (state n u.val v.val (x.val+1) G.bits (liveBits alive) output clock
        (flags [a && cell mode G alive u v x] au av eq edge [] [] [] [] [] [])) 1 := by
    convert push_executes g (6 : Fin 23) true
      (state n u.val v.val x.val G.bits (liveBits alive) output clock
        (flags [a && cell mode G alive u v x] au av eq edge [] [] [] [] [] [])) using 1
    funext i;fin_cases i <;> simp [state,flags,List.replicate_succ]
  refine ⟨t1+(t2+(t3+(t4+(t5+(16+(3+1+2)+2)+2)+2)+2)+2)+2,
    seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3
      (seq_executes _ _ g h4 (seq_executes _ _ g h5 (seq_executes _ _ g h6
        (seq_executes _ _ g h7 h8)))))),?_⟩
  have hN : 1≤(n+1)^2 := Nat.one_le_pow 2 (n+1) (by omega)
  omega

lemma body_queryFree (mode : Bool) : (body mode).QueryFree :=
  seq_queryFree _ _ readX_queryFree (seq_queryFree _ _ compareXU_queryFree
    (seq_queryFree _ _ compareXV_queryFree (seq_queryFree _ _ readVX_queryFree
      (seq_queryFree _ _ readUX_queryFree (seq_queryFree _ _
        (GraphVerifier.Runtime.decision_queryFree _ _ _) (seq_queryFree _ _
          (reverseOn_queryFree _ _ _) (push_queryFree _ _)))))))

end HiddenCircuits.DH.Runtime.PairCheck.TestRuntime
