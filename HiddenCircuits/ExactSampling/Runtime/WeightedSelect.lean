import HiddenCircuits.DH.Runtime.WordArrayCore
import HiddenCircuits.Complexity.BinaryArithmetic.SubtractionMachine
import HiddenCircuits.Complexity.OracleMove

/-! Literal binary weighted-interval scanning. All weights and residual ranks
remain binary. Only the selected position is represented in unary. -/
namespace HiddenCircuits.ExactSampling.Runtime.WeightedSelect
open Complexity OracleBlock BinaryArithmetic

/-- The selected position, the residual rank, and a visible successful flag. -/
def select : List ℕ → ℕ → ℕ × ℕ × Bool
  | [],r => (0,r,false)
  | w::ws,r => if r<w then (0,r,true) else
      let q := select ws (r-w)
      (q.1+1,q.2.1,q.2.2)

 theorem select_rank_le (ws : List ℕ) (r : ℕ) : (select ws r).2.1≤r := by
  induction ws generalizing r with
  | nil => rfl
  | cons w ws ih =>
    simp only [select]
    split_ifs
    · exact le_rfl
    · exact (ih (r-w)).trans (Nat.sub_le _ _)

 theorem select_index_le (ws : List ℕ) (r : ℕ) : (select ws r).1≤ws.length := by
  induction ws generalizing r with
  | nil => rfl
  | cons w ws ih =>
    simp only [select,List.length_cons]
    split_ifs
    · omega
    · exact Nat.add_le_add_right (ih _) 1

 theorem select_interval (ws : List ℕ) (j : Fin ws.length) (r : ℕ) (hr : r<ws[j.val]) :
    select ws ((ws.take j.val).sum+r)=(j.val,r,true) := by
  induction ws generalizing r with
  | nil => exact j.elim0
  | cons w ws ih =>
    cases j using Fin.cases with
    | zero =>
      have hrw : r<w := by simpa using hr
      simp [select,hrw]
    | succ j =>
      have he : (w::ws)[j.succ.val]=ws[j.val] := by simp
      rw [he] at hr
      simp only [Fin.val_succ,List.take_succ_cons,List.sum_cons,select]
      rw [if_neg (by omega),show w+(ws.take j.val).sum+r-w=(ws.take j.val).sum+r by omega,
        ih j r hr]

 def state (data rank index word candidate flag parseFlag found : BitString) : Store 10 := fun i =>
  if i.val=0 then data else if i.val=1 then rank else if i.val=2 then index
  else if i.val=3 then word else if i.val=4 then candidate else if i.val=6 then flag
  else if i.val=8 then parseFlag else if i.val=10 then found else []

 def store (ws : List ℕ) (r j : ℕ) : Store 10 :=
  state (encodeBitList (ws.map Computability.encodeNat)) (Computability.encodeNat r)
    (List.replicate j true) [] [] [] [] []

 def result (r j : ℕ) (ok : Bool) : Store 10 :=
  state [] (Computability.encodeNat r) (List.replicate j true) [] [] [] [] (if ok then [true] else [])

 def parsePorts : Fin 4 ↪ Fin 11 where
  toFun i := ![0,3,7,8] i
  inj' := by decide +kernel
 def subPorts : Fin 4 ↪ Fin 11 where
  toFun i := ![4,3,5,6] i
  inj' := by decide +kernel

 noncomputable def parse : OracleBlock 10 := GraphVerifier.Runtime.unpairOn parsePorts
 noncomputable def compare : OracleBlock 10 := seq (copyOn 1 4 9 (by decide) (by decide) (by decide))
   (rename subBlock subPorts)
 noncomputable def reject : OracleBlock 10 := seq (clear 1)
   (seq (moveOn 4 1 9 (by decide) (by decide) (by decide)) (push 2 true))
 noncomputable def accept : OracleBlock 10 := seq (clear 4) (seq (clear 0) (push 10 true))
 noncomputable def decision : OracleBlock 10 := branchPop 6 reject reject accept
 noncomputable def body : OracleBlock 10 := seq parse (seq (clear 8) (seq compare decision))
 noncomputable def program : OracleBlock 10 := whilePop 0 body body

 theorem parse_executes (g : BitString→ℕ) (data rank index word : BitString) :
    parse.Executes g (state (pairBits word data) rank index [] [] [] [] [])
      (state data rank index word [] [] [true] []) (5*word.length+3) := by
  have h := GraphVerifier.Runtime.unpairOn_executes parsePorts g
    (state (pairBits word data) rank index [] [] [] [] [])
    (state data rank index word [] [] [true] []) (pairBits word data)
    (by funext i;fin_cases i <;> rfl)
    (by funext i;fin_cases i <;> simp only [GraphVerifier.parse_pair] <;> rfl)
    (by intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | exact (hi 2 rfl).elim | exact (hi 3 rfl).elim)
  convert h using 1
  simp [GraphVerifier.parse_pair,pair_parse_cost];omega

 theorem compare_executes (g : BitString→ℕ) (data index : BitString) (r w : ℕ) :
    compare.Executes g (state data (Computability.encodeNat r) index (Computability.encodeNat w) [] [] [] [])
      (state data (Computability.encodeNat r) index [] (Computability.encodeNat (r-w)) [decide (r<w)] [] [])
      (5*Nat.size r+2+subCost (Computability.encodeNat r) (Computability.encodeNat w)+2) := by
  have hc : (copyOn (1:Fin 11) 4 9 (by decide) (by decide) (by decide)).Executes g
      (state data (Computability.encodeNat r) index (Computability.encodeNat w) [] [] [] [])
      (state data (Computability.encodeNat r) index (Computability.encodeNat w) (Computability.encodeNat r) [] [] [])
      (5*Nat.size r+2) := by
    convert copyOn_executes g (1:Fin 11) 4 9 (by decide) (by decide) (by decide)
      (state data (Computability.encodeNat r) index (Computability.encodeNat w) [] [] [] []) rfl using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state,encodeNat_length]
  have hs : (rename subBlock subPorts).Executes g
      (state data (Computability.encodeNat r) index (Computability.encodeNat w) (Computability.encodeNat r) [] [] [])
      (state data (Computability.encodeNat r) index [] (Computability.encodeNat (r-w)) [decide (r<w)] [] [])
      (subCost (Computability.encodeNat r) (Computability.encodeNat w)) := by
    apply rename_executes_to subBlock subPorts g (subBlock_encode g r w)
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | exact (hi 2 rfl).elim | exact (hi 3 rfl).elim
  exact seq_executes _ _ g hc hs

 theorem reject_executes (g : BitString→ℕ) (data : BitString) (r j w : ℕ) :
    reject.Executes g (state data (Computability.encodeNat r) (List.replicate j true) []
        (Computability.encodeNat (r-w)) [] [] [])
      (state data (Computability.encodeNat (r-w)) (List.replicate (j+1) true) [] [] [] [] [])
      (Nat.size r+6*Nat.size (r-w)+11) := by
  have hc : (clear (1:Fin 11)).Executes g
      (state data (Computability.encodeNat r) (List.replicate j true) [] (Computability.encodeNat (r-w)) [] [] [])
      (state data [] (List.replicate j true) [] (Computability.encodeNat (r-w)) [] [] []) (Nat.size r+1) := by
    convert clear_executes g (1:Fin 11) _ using 1
    · funext i;fin_cases i <;> rfl
    · simp [state,encodeNat_length]
  have hm : (moveOn (4:Fin 11) 1 9 (by decide) (by decide) (by decide)).Executes g
      (state data [] (List.replicate j true) [] (Computability.encodeNat (r-w)) [] [] [])
      (state data (Computability.encodeNat (r-w)) (List.replicate j true) [] [] [] [] [])
      (6*Nat.size (r-w)+5) := by
    convert moveOn_executes g (4:Fin 11) 1 9 (by decide) (by decide) (by decide)
      (state data [] (List.replicate j true) [] (Computability.encodeNat (r-w)) [] [] []) rfl using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state,encodeNat_length]
  have hp : (push (2:Fin 11) true).Executes g
      (state data (Computability.encodeNat (r-w)) (List.replicate j true) [] [] [] [] [])
      (state data (Computability.encodeNat (r-w)) (List.replicate (j+1) true) [] [] [] [] []) 1 := by
    convert push_executes g (2:Fin 11) true _ using 1
    funext i;fin_cases i <;> simp [state,List.replicate_succ]
  convert seq_executes _ _ g hc (seq_executes _ _ g hm hp) using 1 <;> omega

 theorem accept_executes (g : BitString→ℕ) (data : BitString) (r j w : ℕ) :
    accept.Executes g (state data (Computability.encodeNat r) (List.replicate j true) []
        (Computability.encodeNat (r-w)) [] [] [])
      (result r j true) (Nat.size (r-w)+data.length+7) := by
  have hc : (clear (4:Fin 11)).Executes g
      (state data (Computability.encodeNat r) (List.replicate j true) [] (Computability.encodeNat (r-w)) [] [] [])
      (state data (Computability.encodeNat r) (List.replicate j true) [] [] [] [] []) (Nat.size (r-w)+1) := by
    convert clear_executes g (4:Fin 11) _ using 1
    · funext i;fin_cases i <;> rfl
    · simp [state,encodeNat_length]
  have hd : (clear (0:Fin 11)).Executes g
      (state data (Computability.encodeNat r) (List.replicate j true) [] [] [] [] [])
      (state [] (Computability.encodeNat r) (List.replicate j true) [] [] [] [] []) (data.length+1) := by
    convert clear_executes g (0:Fin 11) _ using 1
    funext i;fin_cases i <;> rfl
  have hp : (push (10:Fin 11) true).Executes g
      (state [] (Computability.encodeNat r) (List.replicate j true) [] [] [] [] []) (result r j true) 1 := by
    convert push_executes g (10:Fin 11) true _ using 1
    funext i;fin_cases i <;> rfl
  convert seq_executes _ _ g hc (seq_executes _ _ g hd hp) using 1 <;> omega

 theorem body_executes (g : BitString→ℕ) (ws : List ℕ) (r j w : ℕ) :
    ∃t,body.Executes g
      (state (pairBits (Computability.encodeNat w) (encodeBitList (ws.map Computability.encodeNat)))
        (Computability.encodeNat r) (List.replicate j true) [] [] [] [] [])
      (if r<w then result r j true else store ws (r-w) (j+1)) t ∧
      t≤40*(Nat.size r+Nat.size w+1)+(encodeBitList (ws.map Computability.encodeNat)).length := by
  let data := encodeBitList (ws.map Computability.encodeNat)
  have hp := parse_executes g data (Computability.encodeNat r) (List.replicate j true) (Computability.encodeNat w)
  have hc : (clear (8:Fin 11)).Executes g
      (state data (Computability.encodeNat r) (List.replicate j true) (Computability.encodeNat w) [] [] [true] [])
      (state data (Computability.encodeNat r) (List.replicate j true) (Computability.encodeNat w) [] [] [] []) 2 := by
    convert clear_executes g (8:Fin 11) _ using 1
    funext i;fin_cases i <;> rfl
  have hcmp := compare_executes g data (List.replicate j true) r w
  have hsub := subCost_bound (Computability.encodeNat r) (Computability.encodeNat w)
  simp only [encodeNat_length] at hsub
  have hsize := Nat.size_le_size (Nat.sub_le r w)
  have hm : max (Nat.size r) (Nat.size w)≤Nat.size r+Nat.size w := by omega
  by_cases ha : r<w
  · have hd : decision.Executes g
        (state data (Computability.encodeNat r) (List.replicate j true) [] (Computability.encodeNat (r-w)) [decide (r<w)] [] [])
        (result r j true) (Nat.size (r-w)+data.length+7+2) := by
      apply branchPop_true (6:Fin 11) reject reject accept g (rest:=[]) (by simp [state,ha])
      convert accept_executes g data r j w using 1
      funext i;fin_cases i <;> simp [state]
    refine ⟨(5*(Computability.encodeNat w).length+3)+(2+((5*Nat.size r+2+
      subCost (Computability.encodeNat r) (Computability.encodeNat w)+2)+
      (Nat.size (r-w)+data.length+7+2)+2)+2)+2,?_,?_⟩
    · simpa [ha] using seq_executes _ _ g hp (seq_executes _ _ g hc (seq_executes _ _ g hcmp hd))
    · simp only [encodeNat_length] at *
      dsimp only [data] at *
      omega
  · have hd : decision.Executes g
        (state data (Computability.encodeNat r) (List.replicate j true) [] (Computability.encodeNat (r-w)) [decide (r<w)] [] [])
        (store ws (r-w) (j+1)) (Nat.size r+6*Nat.size (r-w)+11+2) := by
      apply branchPop_false (6:Fin 11) reject reject accept g (rest:=[]) (by simp [state,ha])
      convert reject_executes g data r j w using 1
      funext i;fin_cases i <;> simp [state]
    refine ⟨(5*(Computability.encodeNat w).length+3)+(2+((5*Nat.size r+2+
      subCost (Computability.encodeNat r) (Computability.encodeNat w)+2)+
      (Nat.size r+6*Nat.size (r-w)+11+2)+2)+2)+2,?_,?_⟩
    · simpa [ha] using seq_executes _ _ g hp (seq_executes _ _ g hc (seq_executes _ _ g hcmp hd))
    · simp only [encodeNat_length] at *
      dsimp only [data] at *
      omega

/-- The loop runs on arbitrary nonnegative binary weights, including zeros. -/
theorem loop_executes (g : BitString→ℕ) (ws : List ℕ) (r j : ℕ) :
    ∃t,WhileExecution (0:Fin 11) body body g (store ws r j)
      (result (select ws r).2.1 (j+(select ws r).1) (select ws r).2.2) t ∧
      t≤(ws.length+1)*(60*((encodeBitList (ws.map Computability.encodeNat)).length+Nat.size r+1)+60) := by
  induction ws generalizing r j with
  | nil =>
    refine ⟨1,?_,?_⟩
    · simpa [store,result,select,encodeBitList] using
        (WhileExecution.empty (stack:=(0:Fin 11)) (B:=body) (C:=body) (g:=g) (store [] r j) rfl)
    · simp
  | cons w ws ih =>
    obtain ⟨c,hc,hcb⟩ := body_executes g ws r j w
    have hs : Function.update (store (w::ws) r j) (0:Fin 11)
        (pairBits (Computability.encodeNat w) (encodeBitList (ws.map Computability.encodeNat)))=
        state (pairBits (Computability.encodeNat w) (encodeBitList (ws.map Computability.encodeNat)))
          (Computability.encodeNat r) (List.replicate j true) [] [] [] [] [] := by
      funext i;fin_cases i <;> simp [store,state]
    have hlen : (encodeBitList ((w::ws).map Computability.encodeNat)).length=
        2*Nat.size w+(encodeBitList (ws.map Computability.encodeNat)).length+2 := by
      simp [encodeBitList,encodeNat_length]
    by_cases ha : r<w
    · rw [if_pos ha] at hc
      have ht : WhileExecution (0:Fin 11) body body g (result r j true) (result r j true) 1 :=
        WhileExecution.empty _ rfl
      have hh := WhileExecution.one (stack:=(0:Fin 11)) (B:=body) (C:=body)
        (s:=store (w::ws) r j) (g:=g) rfl (by rw [hs];exact hc) ht
      refine ⟨1+c+1+1,?_,?_⟩
      · simpa [select,ha] using hh
      · rw [List.length_cons,hlen]
        nlinarith
    · rw [if_neg ha] at hc
      obtain ⟨t,ht,htb⟩ := ih (r-w) (j+1)
      have hh := WhileExecution.one (stack:=(0:Fin 11)) (B:=body) (C:=body)
        (s:=store (w::ws) r j) (g:=g) rfl (by rw [hs];exact hc) ht
      refine ⟨1+c+1+t,?_,?_⟩
      · simpa [select,ha,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
      · have hr := Nat.size_le_size (Nat.sub_le r w)
        have ht' : t≤(ws.length+1)*(60*((encodeBitList ((w::ws).map Computability.encodeNat)).length+Nat.size r+1)+60) := by
          apply htb.trans
          gcongr
          rw [hlen]
          omega
        rw [hlen] at ht'
        rw [List.length_cons,hlen]
        nlinarith

 theorem program_executes (g : BitString→ℕ) (ws : List ℕ) (r j : ℕ) :
    ∃t,program.Executes g (store ws r j)
      (result (select ws r).2.1 (j+(select ws r).1) (select ws r).2.2) t ∧
      t≤(ws.length+1)*(60*((encodeBitList (ws.map Computability.encodeNat)).length+Nat.size r+1)+60) := by
  obtain ⟨t,ht,hb⟩ := loop_executes g ws r j
  exact ⟨t,whilePop_executes _ _ _ g ht,hb⟩

 theorem program_queryFree : program.QueryFree := by
  have hr : reject.QueryFree := seq_queryFree _ _ (clear_queryFree _)
    (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _) (push_queryFree _ _))
  have ha : accept.QueryFree := seq_queryFree _ _ (clear_queryFree _)
    (seq_queryFree _ _ (clear_queryFree _) (push_queryFree _ _))
  have hc : compare.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (rename_queryFree _ _ subBlock_queryFree)
  have hb : body.QueryFree := seq_queryFree _ _ (GraphVerifier.Runtime.unpairOn_queryFree _)
    (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ hc (branchPop_queryFree _ _ _ _ hr hr ha)))
  exact whilePop_queryFree _ _ _ hb hb

end HiddenCircuits.ExactSampling.Runtime.WeightedSelect
