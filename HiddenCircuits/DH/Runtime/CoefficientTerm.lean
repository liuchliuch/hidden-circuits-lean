import HiddenCircuits.DH.Runtime.CoefficientTermIndex
import HiddenCircuits.DH.Runtime.ScalarCoefficientGuard
import HiddenCircuits.DH.Runtime.WordArray

/-! A term is computed from two actual cached row
serializations, unary indices, physical index guards, and literal arithmetic. -/
namespace HiddenCircuits.DH.Runtime.CoefficientTerm
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic PruningModel CoefficientRow Polynomial
set_option maxHeartbeats 1600000

def state (left right : List ℕ) (i j r k : ℕ) (out a b flag : BitString) : Store 29:=fun q=>
  if q.val=0 then List.replicate i true else if q.val=1 then List.replicate j true
  else if q.val=2 then List.replicate r true else if q.val=3 then List.replicate k true
  else if q.val=4 then rowBits left else if q.val=5 then rowBits right else if q.val=6 then out
  else if q.val=7 then a else if q.val=8 then b else if q.val=9 then flag else []
def store (left right : List ℕ) (i j r k : ℕ) (out : BitString) : Store 29:=state left right i j r k out [] [] []
def leftMap : Fin 8↪Fin 30:=⟨fun q=>![4,0,7,10,11,12,13,14] q,by decide +kernel⟩
def rightMap : Fin 8↪Fin 30:=⟨fun q=>![5,1,8,10,11,12,13,14] q,by decide +kernel⟩
def indexMap : Fin 10↪Fin 30:=⟨fun q=>![0,1,2,3,9,10,11,12,13,14] q,by decide +kernel⟩
def scalarMap : Fin 26↪Fin 30 where
  toFun q:=⟨if q.val<3 then q.val else if q.val=3 then 7 else if q.val=4 then 8 else if q.val=5 then 6 else q.val+4,by split_ifs <;> omega⟩
  inj':=by
    intro q z h;apply Fin.ext;have hh:=congrArg Fin.val h
    change (if q.val<3 then q.val else if q.val=3 then 7 else if q.val=4 then 8 else if q.val=5 then 6 else q.val+4)=
      (if z.val<3 then z.val else if z.val=3 then 7 else if z.val=4 then 8 else if z.val=5 then 6 else z.val+4) at hh
    split_ifs at hh <;> omega
noncomputable def accepted : OracleBlock 29:=seq (WordArray.readOn leftMap) (seq (WordArray.readOn rightMap)
  (seq (ScalarCoefficient.on scalarMap) (seq (clear 7) (clear 8))))
noncomputable def program (kind : Kind) : OracleBlock 29:=seq (CoefficientTermIndex.on indexMap kind)
  (branchPop 9 (push 6 false) (push 6 false) accepted)
noncomputable def time : Polynomial ℕ:=ScalarCoefficient.guardedTime.comp (3*X)+2000*(X+1)^2

lemma row_get (xs : List ℕ) (q : ℕ) (hq:q<xs.length) :
    (rowWords xs)[q]?.getD []=signedBits (CoefficientModel.read xs q:ℤ):=by
  simp [rowWords,CoefficientModel.read,List.getElem?_eq_getElem,hq]
lemma accepted_executes (g : BitString→ ℕ) (n : ℕ) (left right : List ℕ) (i j r k : ℕ)
    (hi:i<left.length) (hj:j<right.length) (hin:i≤ n) (hjn:j≤ n) (hrn:r≤ n) :
    ∃t,accepted.Executes g (store left right i j r k [])
      (store left right i j r k (signedBits (CoefficientModel.read left i*CoefficientModel.read right j*
        (i.choose r*j.choose r*r.factorial):ℕ))) t ∧
      t≤ ScalarCoefficient.guardedTime.eval (3*inputSize n left right)+1000*(inputSize n left right+1)^2 := by
  let A:=CoefficientModel.read left i
  let B:=CoefficientModel.read right j
  let Aw:=signedBits (A:ℤ)
  let Bw:=signedBits (B:ℤ)
  let out:=signedBits (A*B*(i.choose r*j.choose r*r.factorial):ℕ)
  have hA:Aw.length≤(rowBits left).length:=read_word_length left i hi
  have hB:Bw.length≤(rowBits right).length:=read_word_length right j hj
  obtain ⟨a,ha,hab⟩:=WordArray.readOn_executes leftMap g (store left right i j r k []) (rowWords left) i
    (by funext q;fin_cases q <;> rfl)
  rw [row_get left i hi] at ha
  have ha':(WordArray.readOn leftMap).Executes g (store left right i j r k []) (state left right i j r k [] Aw [] []) a:=by
    convert ha using 1;funext q;fin_cases q <;> rfl
  obtain ⟨b,hb,hbb⟩:=WordArray.readOn_executes rightMap g (state left right i j r k [] Aw [] []) (rowWords right) j
    (by funext q;fin_cases q <;> rfl)
  rw [row_get right j hj] at hb
  have hb':(WordArray.readOn rightMap).Executes g (state left right i j r k [] Aw [] []) (state left right i j r k [] Aw Bw []) b:=by
    convert hb using 1;funext q;fin_cases q <;> rfl
  obtain ⟨c,hc,hcb⟩:=ScalarCoefficient.on_executes scalarMap g (state left right i j r k [] Aw Bw []) i j r A B
    (by funext q;fin_cases q <;> rfl)
  have hc':(ScalarCoefficient.on scalarMap).Executes g (state left right i j r k [] Aw Bw []) (state left right i j r k out Aw Bw []) c:=by
    convert hc using 1;funext q;fin_cases q <;> rfl
  have hd:(clear (7:Fin 30)).Executes g (state left right i j r k out Aw Bw [])
      (state left right i j r k out [] Bw []) (Aw.length+1):=by
    convert clear_executes g (7:Fin 30) (state left right i j r k out Aw Bw []) using 1
    funext q;fin_cases q <;> rfl
  have he:(clear (8:Fin 30)).Executes g (state left right i j r k out [] Bw [])
      (store left right i j r k out) (Bw.length+1):=by
    convert clear_executes g (8:Fin 30) (state left right i j r k out [] Bw []) using 1
    funext q;fin_cases q <;> rfl
  refine ⟨_,seq_executes _ _ g ha' (seq_executes _ _ g hb' (seq_executes _ _ g hc' (seq_executes _ _ g hd he))),?_⟩
  have hS:ScalarCoefficient.inputSize i j r A B≤ 3*inputSize n left right:=by
    unfold ScalarCoefficient.inputSize inputSize;dsimp [Aw,Bw] at hA hB;omega
  have hm:=polynomial_nat_eval_mono ScalarCoefficient.guardedTime hS
  dsimp only at hm
  have hLa:(rowBits left).length≤ inputSize n left right:=by unfold inputSize;omega
  have hLb:(rowBits right).length≤ inputSize n left right:=by unfold inputSize;omega
  have hN:n≤ inputSize n left right:=by unfold inputSize;omega
  change a≤ GraphReduction.Runtime.lookupBound (rowBits left).length i at hab
  change b≤ GraphReduction.Runtime.lookupBound (rowBits right).length j at hbb
  have hba:a≤ 100*(inputSize n left right+1)^2:=by
    unfold GraphReduction.Runtime.lookupBound at hab
    have hm1: (i+1)*(6*(rowBits left).length+14)≤(inputSize n left right+1)*(6*inputSize n left right+14):=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have hbb':b≤ 100*(inputSize n left right+1)^2:=by
    unfold GraphReduction.Runtime.lookupBound at hbb
    have hm1: (j+1)*(6*(rowBits right).length+14)≤(inputSize n left right+1)*(6*inputSize n left right+14):=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  nlinarith

lemma pop_flag (left right : List ℕ) (i j r k : ℕ) (b : Bool) :
    Function.update (state left right i j r k [] [] [] [b]) 9 []=store left right i j r k []:=by
  funext q;fin_cases q <;> rfl

theorem executes (g : BitString→ ℕ) (n : ℕ) (kind : Kind) (left right : List ℕ) (i j r k : ℕ)
    (hi:i<left.length) (hj:j<right.length) (hin:i≤ n) (hjn:j≤ n) (hrn:r≤ n) (hkn:k≤ n) :
    ∃t,(program kind).Executes g (store left right i j r k [])
      (store left right i j r k (signedBits (UniformCoefficientModel.contribution kind left right k i j r:ℕ))) t ∧
      t≤ time.eval (inputSize n left right) := by
  obtain ⟨c,hc,hcb⟩:=CoefficientTermIndex.on_executes indexMap g (store left right i j r k []) kind i j r k
    (by funext q;fin_cases q <;> rfl)
  have hc':(CoefficientTermIndex.on indexMap kind).Executes g (store left right i j r k [])
      (state left right i j r k [] [] [] [decide (UniformCoefficientModel.test kind i j r k)]) c:=by
    convert hc using 1;funext q;fin_cases q <;> rfl
  by_cases hp:UniformCoefficientModel.test kind i j r k
  · simp only [hp,decide_true] at hc'
    obtain ⟨t,ht,htb⟩:=accepted_executes g n left right i j r k hi hj hin hjn hrn
    have hb:(branchPop (9:Fin 30) (push 6 false) (push 6 false) accepted).Executes g
        (state left right i j r k [] [] [] [true])
        (store left right i j r k (signedBits (CoefficientModel.read left i*CoefficientModel.read right j*(i.choose r*j.choose r*r.factorial):ℕ))) (t+2):=by
      apply branchPop_true _ _ _ _ g rfl;rw [pop_flag];exact ht
    simp only [UniformCoefficientModel.contribution,if_pos hp]
    refine ⟨_,seq_executes _ _ g hc' hb,?_⟩
    simp only [time,eval_add,eval_comp,eval_mul,eval_X,eval_ofNat,eval_pow,eval_one]
    have hN:n≤ inputSize n left right:=by unfold inputSize;omega
    nlinarith
  · simp only [hp,decide_false] at hc'
    have hb:(branchPop (9:Fin 30) (push 6 false) (push 6 false) accepted).Executes g
        (state left right i j r k [] [] [] [false]) (store left right i j r k (signedBits (0:ℤ))) 3:=by
      apply branchPop_false _ _ _ _ g rfl;rw [pop_flag]
      convert push_executes g (6:Fin 30) false (store left right i j r k []) using 1
      funext q;fin_cases q <;> rfl
    simp only [UniformCoefficientModel.contribution,if_neg hp]
    refine ⟨_,seq_executes _ _ g hc' hb,?_⟩
    simp only [time,eval_add,eval_comp,eval_mul,eval_X,eval_ofNat,eval_pow,eval_one]
    have hN:n≤ inputSize n left right:=by unfold inputSize;omega
    nlinarith
lemma accepted_queryFree : accepted.QueryFree:=seq_queryFree _ _ (WordArray.readOn_queryFree _)
  (seq_queryFree _ _ (WordArray.readOn_queryFree _) (seq_queryFree _ _ (ScalarCoefficient.on_queryFree _)
    (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _))))
lemma queryFree (kind : Kind) : (program kind).QueryFree:=seq_queryFree _ _ (CoefficientTermIndex.on_queryFree _ _)
  (branchPop_queryFree _ _ _ _ (push_queryFree _ _) (push_queryFree _ _) accepted_queryFree)
noncomputable def on {l : ℕ} (φ : Fin 30↪Fin (l+1)) (kind : Kind) : OracleBlock l:=rename (program kind) φ
lemma on_executes {l : ℕ} (φ : Fin 30↪Fin (l+1)) (g : BitString→ ℕ) (s : Store l)
    (n : ℕ) (kind : Kind) (left right : List ℕ) (i j r k : ℕ)
    (hi:i<left.length) (hj:j<right.length) (hin:i≤ n) (hjn:j≤ n) (hrn:r≤ n) (hkn:k≤ n)
    (hs:s∘φ=store left right i j r k []) :
    ∃t,(on φ kind).Executes g s
      (Function.update s (φ 6) (signedBits (UniformCoefficientModel.contribution kind left right k i j r:ℕ))) t ∧
      t≤ time.eval (inputSize n left right) := by
  obtain ⟨t,ht,hb⟩:=executes g n kind left right i j r k hi hj hin hjn hrn hkn
  refine ⟨t,?_,hb⟩
  apply rename_executes_to _ φ g ht hs
  · have he:(Function.update s (φ 6) (signedBits (UniformCoefficientModel.contribution kind left right k i j r:ℕ)))∘φ=
        Function.update (s∘φ) 6 (signedBits (UniformCoefficientModel.contribution kind left right k i j r:ℕ)):=by
      funext q;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext q;fin_cases q <;> rfl
  · intro q hq;exact Function.update_of_ne (hq 6).symm _ _
lemma on_queryFree {l : ℕ} (φ : Fin 30↪Fin (l+1)) (kind : Kind) : (on φ kind).QueryFree:=rename_queryFree _ _ (queryFree kind)
end HiddenCircuits.DH.Runtime.CoefficientTerm
