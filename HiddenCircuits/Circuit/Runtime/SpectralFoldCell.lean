import HiddenCircuits.Circuit.Runtime.SpectralVectorCombineFrame
import HiddenCircuits.Circuit.Runtime.SpectralTableData

/-! One actual nested-table fold parses a scale and a coefficient row, then
executes every entry of the vector multiply-add and restores the accumulator. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralFold
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic Polynomial

def state (acc scales rows scale row flag : BitString) : Store 24 := fun i =>
  if i.val=0 then scale else if i.val=1 then row else if i.val=2 then acc
  else if i.val=21 then rows else if i.val=22 then scales else if i.val=23 then flag else []
 def scaleEmbedding : Fin 4 ↪ Fin 25 where
  toFun i := if i.val=0 then 22 else if i.val=1 then 0 else if i.val=2 then 24 else 23
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
 def rowEmbedding : Fin 4 ↪ Fin 25 where
  toFun i := if i.val=0 then 21 else if i.val=1 then 1 else if i.val=2 then 24 else 23
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
 def vectorEmbedding : Fin 21 ↪ Fin 25 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun z : Fin 25 => z.val) h)
noncomputable def parseScale : OracleBlock 24 := GraphVerifier.Runtime.unpairOn scaleEmbedding
noncomputable def parseRow : OracleBlock 24 := GraphVerifier.Runtime.unpairOn rowEmbedding
noncomputable def combine : OracleBlock 24 := SpectralVectorCombine.programOn vectorEmbedding
noncomputable def rowBody : OracleBlock 24 := seq parseRow (seq (clear 23)
  (seq combine (moveOn 0 2 3 (by decide) (by decide) (by decide))))
noncomputable def body : OracleBlock 24 := seq parseScale (seq (clear 23) (branchPop 21 skip skip rowBody))
noncomputable def bodyTime : Polynomial ℕ := SpectralVectorCombine.time.comp (3*X)+6*X*(8*X+20)+10*X+40

 theorem parseScale_executes (oracle : BitString → ℕ) (acc qs rows q : BitString) :
    parseScale.Executes oracle (state acc (pairBits q qs) rows [] [] [])
      (state acc qs rows q [] [true]) (5*q.length+3) := by
  have h := GraphVerifier.Runtime.unpairOn_executes scaleEmbedding oracle
    (state acc (pairBits q qs) rows [] [] []) (state acc qs rows q [] [true]) (pairBits q qs)
    (by funext i;fin_cases i <;> rfl)
    (by funext i;fin_cases i <;> simp only [GraphVerifier.parse_pair] <;> rfl)
    (by intro j hj;fin_cases j <;> first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) | exact False.elim (hj 3 rfl))
  convert h using 1
  simp [GraphVerifier.parse_pair,pair_parse_cost];omega

 theorem parseRow_executes (oracle : BitString → ℕ) (acc qs rows q row : BitString) :
    parseRow.Executes oracle (state acc qs (pairBits row rows) q [] [])
      (state acc qs rows q row [true]) (5*row.length+3) := by
  have h := GraphVerifier.Runtime.unpairOn_executes rowEmbedding oracle
    (state acc qs (pairBits row rows) q [] []) (state acc qs rows q row [true]) (pairBits row rows)
    (by funext i;fin_cases i <;> rfl)
    (by funext i;fin_cases i <;> simp only [GraphVerifier.parse_pair] <;> rfl)
    (by intro j hj;fin_cases j <;> first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) | exact False.elim (hj 3 rfl))
  convert h using 1
  simp [GraphVerifier.parse_pair,pair_parse_cost];omega

 def update (q : ℤ) (xs acc : List ℤ) : List ℤ := List.zipWith (fun x y => y+q*x) xs acc

 theorem combine_executes (oracle : BitString → ℕ) (q : ℤ) (xs acc : List ℤ) (hlen : xs.length=acc.length)
    (qs rows : BitString) :
    ∃ t, combine.Executes oracle
      (state (encodeBitList (acc.map signedBits)) qs rows (signedBits q) (encodeBitList (xs.map signedBits)) [])
      (state [] qs rows (encodeBitList ((update q xs acc).map signedBits)) [] []) t ∧
      t≤SpectralVectorCombine.time.eval ((signedBits q).length+(encodeBitList (xs.map signedBits)).length+
        (encodeBitList (acc.map signedBits)).length) := by
  obtain ⟨t,ht,hb⟩ := SpectralVectorCombine.programOn_executes vectorEmbedding oracle
    (state (encodeBitList (acc.map signedBits)) qs rows (signedBits q) (encodeBitList (xs.map signedBits)) [])
    q xs acc hlen (by funext i;fin_cases i <;> rfl)
  refine ⟨t,?_,hb⟩
  convert ht using 1
  funext i;fin_cases i <;> simp [state,vectorEmbedding,update]

 theorem update_stream_bound (q : ℤ) (xs acc : List ℤ) (hlen : xs.length=acc.length) (B : ℕ)
    (hq : (signedBits q).length≤B) (hx : (encodeBitList (xs.map signedBits)).length≤B)
    (ha : (encodeBitList (acc.map signedBits)).length≤B) :
    (encodeBitList ((update q xs acc).map signedBits)).length≤B*(8*B+20) := by
  have hh := SpectralVectorCombine.output_stream_bound q (xs.zip acc) B hq (by
    intro p hp
    have hx' : p.1∈xs := by
      have hmem : p.1∈(xs.zip acc).map Prod.fst := List.mem_map.mpr ⟨p,hp,rfl⟩
      rwa [List.map_fst_zip hlen.le] at hmem
    have ha' : p.2∈acc := by
      have hmem : p.2∈(xs.zip acc).map Prod.snd := List.mem_map.mpr ⟨p,hp,rfl⟩
      rwa [List.map_snd_zip hlen.ge] at hmem
    exact ⟨(member_length_le_encodeBitList (List.mem_map.mpr ⟨p.1,hx',rfl⟩)).trans hx,
      (member_length_le_encodeBitList (List.mem_map.mpr ⟨p.2,ha',rfl⟩)).trans ha⟩)
  have he : SpectralVectorCombine.output q (xs.zip acc)=update q xs acc := by
    change (xs.zip acc).map (fun p : ℤ×ℤ => p.2+q*p.1)=_
    exact List.map_uncurry_zip_eq_zipWith (f:=fun x y : ℤ => y+q*x) (l:=xs) (l':=acc)
  rw [he] at hh
  apply hh.trans
  apply Nat.mul_le_mul_right
  have hlen' := list_length_le_encodeBitList_length (xs.map signedBits)
  simp only [List.length_map] at hlen'
  have hz : (xs.zip acc).length≤xs.length := by simp
  omega

 theorem rowBody_executes (oracle : BitString → ℕ) (q : ℤ) (xs acc : List ℤ) (hlen : xs.length=acc.length)
    (qs rows : BitString) (B : ℕ) (hq : (signedBits q).length≤B)
    (hx : (encodeBitList (xs.map signedBits)).length≤B) (ha : (encodeBitList (acc.map signedBits)).length≤B) :
    ∃ t, rowBody.Executes oracle
      (state (encodeBitList (acc.map signedBits)) qs (pairBits (encodeBitList (xs.map signedBits)) rows) (signedBits q) [] [])
      (state (encodeBitList ((update q xs acc).map signedBits)) qs rows [] [] []) t ∧
      t≤SpectralVectorCombine.time.eval (3*B)+6*B*(8*B+20)+5*B+22 := by
  let a := encodeBitList (acc.map signedBits)
  let x := encodeBitList (xs.map signedBits)
  let v := encodeBitList ((update q xs acc).map signedBits)
  have h₁ := parseRow_executes oracle a qs rows (signedBits q) x
  have h₂ : (clear (23:Fin 25)).Executes oracle (state a qs rows (signedBits q) x [true])
      (state a qs rows (signedBits q) x []) 2 := by
    convert clear_executes oracle (23:Fin 25) (state a qs rows (signedBits q) x [true]) using 1
    funext i;fin_cases i <;> rfl
  obtain ⟨t,ht,hb⟩ := combine_executes oracle q xs acc hlen qs rows
  have h₄ : (moveOn (0:Fin 25) 2 3 (by decide) (by decide) (by decide)).Executes oracle
      (state [] qs rows v [] []) (state v qs rows [] [] []) (6*v.length+5) := by
    convert moveOn_executes oracle (0:Fin 25) 2 3 (by decide) (by decide) (by decide) (state [] qs rows v [] []) rfl using 1
    funext i;fin_cases i <;> simp [state]
  have hm := polynomial_nat_eval_mono SpectralVectorCombine.time (show
    (signedBits q).length+(encodeBitList (xs.map signedBits)).length+(encodeBitList (acc.map signedBits)).length≤3*B by omega)
  have hv := update_stream_bound q xs acc hlen B hq hx ha
  refine ⟨(5*x.length+3)+(2+(t+(6*v.length+5)+2)+2)+2,
    seq_executes _ _ oracle h₁ (seq_executes _ _ oracle h₂ (seq_executes _ _ oracle ht h₄)),?_⟩
  dsimp [x,v]
  nlinarith

 theorem body_executes (oracle : BitString → ℕ) (q : ℤ) (xs acc : List ℤ) (hlen : xs.length=acc.length)
    (qs rows : BitString) (B : ℕ) (hq : (signedBits q).length≤B)
    (hx : (encodeBitList (xs.map signedBits)).length≤B) (ha : (encodeBitList (acc.map signedBits)).length≤B) :
    ∃ t, body.Executes oracle
      (state (encodeBitList (acc.map signedBits)) (pairBits (signedBits q) qs)
        (true::pairBits (encodeBitList (xs.map signedBits)) rows) [] [] [])
      (state (encodeBitList ((update q xs acc).map signedBits)) qs rows [] [] []) t ∧ t≤bodyTime.eval B := by
  let a := encodeBitList (acc.map signedBits)
  let x := encodeBitList (xs.map signedBits)
  let s₁ := state a qs (true::pairBits x rows) (signedBits q) [] [true]
  let s₂ := state a qs (true::pairBits x rows) (signedBits q) [] []
  have h₁ := parseScale_executes oracle a qs (true::pairBits x rows) (signedBits q)
  have h₂ : (clear (23:Fin 25)).Executes oracle s₁ s₂ 2 := by
    convert clear_executes oracle (23:Fin 25) s₁ using 1
    funext i;fin_cases i <;> rfl
  obtain ⟨t,ht,hb⟩ := rowBody_executes oracle q xs acc hlen qs rows B hq hx ha
  have he : Function.update s₂ (21:Fin 25) (pairBits x rows)=state a qs (pairBits x rows) (signedBits q) [] [] := by
    funext i;fin_cases i <;> rfl
  have h₃ := branchPop_true (21:Fin 25) skip skip rowBody oracle (s:=s₂) (rest:=pairBits x rows) rfl
    (by rw [he];exact ht)
  refine ⟨(5*(signedBits q).length+3)+(2+(t+2)+2)+2,seq_executes _ _ oracle h₁ (seq_executes _ _ oracle h₂ h₃),?_⟩
  simp only [bodyTime,eval_add,eval_mul,eval_comp,eval_X,eval_ofNat]
  omega

 theorem body_queryFree : body.QueryFree := seq_queryFree _ _ (GraphVerifier.Runtime.unpairOn_queryFree _)
  (seq_queryFree _ _ (clear_queryFree _) (branchPop_queryFree _ _ _ _ skip_queryFree skip_queryFree
    (seq_queryFree _ _ (GraphVerifier.Runtime.unpairOn_queryFree _)
      (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _
        (SpectralVectorCombine.programOn_queryFree _) (moveOn_queryFree _ _ _ _ _ _))))))
end HiddenCircuits.Circuit.Runtime.SpectralFold
