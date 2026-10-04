import HiddenCircuits.DH.Runtime.PairCheckReads

/-! A literal finite-stack closed-neighborhood tally for the unit-interval
recognizer. The only graph data is the ordinary dense Boolean matrix; the mask
is an array of singleton Boolean words. Every read, test, increment and loop
step is physically charged. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRecognitionScore
open Complexity Complexity.OracleBlock DH.Runtime.PairCheck
open DH.Runtime.PairCheck.TestRuntime

def hit {n : ℕ} (G : MatrixData n) (mask : Vector Bool n) (u x : Fin n) : Bool :=
  mask[x.val] && (decide (x=u) || G.edge u x)

def countFrom {n : ℕ} (f : Fin n → Bool) (i : ℕ) : ℕ → ℕ
  | 0 => 0
  | m+1 => (if h:i<n then if f ⟨i,h⟩ then 1 else 0 else 0)+countFrom f (i+1) m

def score {n : ℕ} (G : MatrixData n) (mask : Vector Bool n) (u : Fin n) : ℕ :=
  countFrom (hit G mask u) 0 n

def hitDecision : List Bool → Bool
  | [selected,equal,edge] => selected && (equal || edge)
  | _ => false

noncomputable def decideHit : OracleBlock 22 :=
  GraphVerifier.Runtime.decision 18 [13,14,17] hitDecision
noncomputable def increment : OracleBlock 22 := branchPop 18 skip skip (push 5 true)
noncomputable def body : OracleBlock 22 := seq readX (seq compareXU
  (seq readUX (seq decideHit (seq increment (push 6 true)))))

def tallyState (n u x count : ℕ) (payload marks clock : BitString) : Store 22 :=
  state n u 0 x payload marks (List.replicate count true) clock
    (flags [] [] [] [] [] [] [] [] [] [] [])

lemma body_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (mask : Vector Bool n) (u x : Fin n) (count : ℕ) (clock : BitString) :
    ∃t, body.Executes g (tallyState n u.val x.val count G.bits (liveBits mask) clock)
      (tallyState n u.val (x.val+1) (count+if hit G mask u x then 1 else 0)
        G.bits (liveBits mask) clock) t ∧ t≤330*(n+1)^2 := by
  let v : Fin n := ⟨0,by have hu := u.isLt; omega⟩
  let out := List.replicate count true
  obtain ⟨t1,h1,b1⟩ := readX_executes g G mask u v x out clock
    (flags [] [] [] [] [] [] [] [] [] [] []) rfl
  have e1 : Function.update (flags [] [] [] [] [] [] [] [] [] [] []) (5 : Fin 11) [mask[x.val]] =
      flags [] [] [] [] [] [mask[x.val]] [] [] [] [] [] := by funext i; fin_cases i <;> rfl
  rw [e1] at h1
  obtain ⟨t2,h2,b2⟩ := compareXU_executes g G mask u v x out clock
    (flags [] [] [] [] [] [mask[x.val]] [] [] [] [] []) rfl
  have e2 : Function.update (flags [] [] [] [] [] [mask[x.val]] [] [] [] [] []) (6 : Fin 11) [decide (x=u)] =
      flags [] [] [] [] [] [mask[x.val]] [decide (x=u)] [] [] [] [] := by funext i; fin_cases i <;> rfl
  rw [e2] at h2
  obtain ⟨t3,h3,b3⟩ := readUX_executes g G mask u v x out clock
    (flags [] [] [] [] [] [mask[x.val]] [decide (x=u)] [] [] [] []) rfl
  have e3 : Function.update (flags [] [] [] [] [] [mask[x.val]] [decide (x=u)] [] [] [] []) (9 : Fin 11) [G.edge u x] =
      flags [] [] [] [] [] [mask[x.val]] [decide (x=u)] [] [] [G.edge u x] [] := by funext i; fin_cases i <;> rfl
  rw [e3] at h3
  let bits : Fin 23 → Bool := fun i => if i.val=13 then mask[x.val]
    else if i.val=14 then decide (x=u) else if i.val=17 then G.edge u x else false
  have h4 : decideHit.Executes g
      (state n u.val 0 x.val G.bits (liveBits mask) out clock
        (flags [] [] [] [] [] [mask[x.val]] [decide (x=u)] [] [] [G.edge u x] []))
      (state n u.val 0 x.val G.bits (liveBits mask) out clock
        (flags [] [] [] [] [] [] [] [] [] [] [hit G mask u x])) 10 := by
    have h := GraphVerifier.Runtime.decision_executes (18 : Fin 23) [13,14,17]
      (by decide) (by decide) hitDecision bits g
      (state n u.val 0 x.val G.bits (liveBits mask) out clock
        (flags [] [] [] [] [] [mask[x.val]] [decide (x=u)] [] [] [G.edge u x] []))
      (by intro i hi;fin_cases i <;> simp [state,flags,bits] at *)
    convert h using 1
    funext i;fin_cases i <;> simp [state,flags,bits,eraseStore,hitDecision,hit]
  have h5 : increment.Executes g
      (state n u.val 0 x.val G.bits (liveBits mask) out clock
        (flags [] [] [] [] [] [] [] [] [] [] [hit G mask u x]))
      (tallyState n u.val x.val (count+if hit G mask u x then 1 else 0)
        G.bits (liveBits mask) clock) 3 := by
    cases hh : hit G mask u x with
    | false =>
      apply branchPop_false 18 skip skip (push 5 true) g rfl
      convert skip_executes g _ using 1
      funext i;fin_cases i <;> simp [tallyState,state,flags,out]
    | true =>
      apply branchPop_true 18 skip skip (push 5 true) g rfl
      convert push_executes g (5 : Fin 23) true _ using 1
      funext i;fin_cases i <;> simp [tallyState,state,flags,out,List.replicate_succ]
  have h6 : (push (6 : Fin 23) true).Executes g
      (tallyState n u.val x.val (count+if hit G mask u x then 1 else 0) G.bits (liveBits mask) clock)
      (tallyState n u.val (x.val+1) (count+if hit G mask u x then 1 else 0) G.bits (liveBits mask) clock) 1 := by
    convert push_executes g (6 : Fin 23) true _ using 1
    funext i;fin_cases i <;> simp [tallyState,state,flags,List.replicate_succ]
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3
    (seq_executes _ _ g h4 (seq_executes _ _ g h5 h6)))),?_⟩
  have hn : 1≤(n+1)^2 := Nat.one_le_pow 2 (n+1) (by omega)
  omega

lemma body_queryFree : body.QueryFree := seq_queryFree _ _ readX_queryFree
  (seq_queryFree _ _ compareXU_queryFree (seq_queryFree _ _ readUX_queryFree
    (seq_queryFree _ _ (GraphVerifier.Runtime.decision_queryFree _ _ _)
      (seq_queryFree _ _ (branchPop_queryFree _ _ _ _ skip_queryFree skip_queryFree
        (push_queryFree _ _)) (push_queryFree _ _)))))

end HiddenCircuits.GraphReduction.Runtime.UnitRecognitionScore
