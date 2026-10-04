import HiddenCircuits.DH.Runtime.CoefficientTerm
import HiddenCircuits.Complexity.BinaryArithmetic.Operations

/-! Physical rectangular-sum accumulator cells, with
invariants on the actual lexicographic prefix of the nonnegative recurrence. -/
namespace HiddenCircuits.DH.Runtime.CoefficientEntry
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic PruningModel CoefficientRow
open UniformCoefficientModel Polynomial
set_option maxHeartbeats 1800000

def state (left right : List ℕ) (a b k i j r ci cj cr : ℕ) (acc term : BitString) : Store 35:=fun q=>
  if q.val=0 then List.replicate a true else if q.val=1 then List.replicate b true
  else if q.val=2 then List.replicate k true else if q.val=3 then rowBits left else if q.val=4 then rowBits right
  else if q.val=5 then acc else if q.val=6 then List.replicate i true else if q.val=7 then List.replicate j true
  else if q.val=8 then List.replicate r true else if q.val=9 then List.replicate cr true
  else if q.val=10 then List.replicate cj true else if q.val=11 then List.replicate ci true
  else if q.val=12 then term else []
def prefixState (kind : Kind) (left right : List ℕ) (a b k i j r ci cj cr : ℕ) : Store 35:=
  state left right a b k i j r ci cj cr (signedBits (prefixValue kind a b left right k i j r:ℕ)) []
def store (left right : List ℕ) (a b k : ℕ) (out : BitString) : Store 35:=state left right a b k 0 0 0 0 0 0 out []
def termMap : Fin 30↪Fin 36 where
  toFun q:=⟨if q.val<3 then 6+q.val else if q.val<6 then q.val-1 else q.val+6,by split_ifs <;> omega⟩
  inj':=by
    intro q z h;apply Fin.ext;have hh:=congrArg Fin.val h
    change (if q.val<3 then 6+q.val else if q.val<6 then q.val-1 else q.val+6)=
      (if z.val<3 then 6+z.val else if z.val<6 then z.val-1 else z.val+6) at hh
    split_ifs at hh <;> omega
def addMap : Fin 9↪Fin 36:=⟨fun q=>![5,12,13,14,15,16,17,18,19] q,by decide +kernel⟩
noncomputable def add : OracleBlock 35:=rename Operation.add.program addMap
noncomputable def cell (kind : Kind) : OracleBlock 35:=seq (CoefficientTerm.on termMap kind) (seq add (push 8 true))
noncomputable def cellTime : Polynomial ℕ:=CoefficientTerm.time+operationTime.comp (2*(2*X^2+5*X+5))+5

lemma wordBound_eq (S : ℕ) : wordBound S=2*S^2+5*S+5:=by
  unfold wordBound entryExponent termExponent;ring
lemma prefix_word_bound (n : ℕ) (kind : Kind) (a b : ℕ) (left right : List ℕ) (k i j r : ℕ)
    (ha:a≤ n) (hb:b≤ n) (hi:i≤ a) (hj:j≤ b) (hr:r≤ a+1) :
    (signedBits (prefixValue kind a b left right k i j r:ℕ)).length≤ wordBound (inputSize n left right):=
  signedBits_length_of_abs_bound (prefix_bound n kind a b left right k i j r ha hb hi hj hr)

theorem cell_executes (g : BitString→ ℕ) (n : ℕ) (kind : Kind) (left right : List ℕ) (a b k i j r ci cj cr : ℕ)
    (ha:a≤ n) (hb:b≤ n) (hk:k≤ n) (hl:left.length=n+1) (hr:right.length=n+1)
    (hi:i≤ a) (hj:j≤ b) (hri:r≤ a) :
    ∃t,(cell kind).Executes g (prefixState kind left right a b k i j r ci cj cr)
      (prefixState kind left right a b k i j (r+1) ci cj cr) t ∧ t≤ cellTime.eval (inputSize n left right) := by
  let P:=prefixValue kind a b left right k i j r
  let C:=contribution kind left right k i j r
  let Q:=prefixValue kind a b left right k i j (r+1)
  have hPQ:P+C=Q:=prefix_step kind a b left right k i j r
  obtain ⟨t,ht,htb⟩:=CoefficientTerm.on_executes termMap g (prefixState kind left right a b k i j r ci cj cr)
    n kind left right i j r k (by omega) (by omega) (by omega) (by omega) (by omega) hk
    (by funext q;fin_cases q <;> rfl)
  let mid:=state left right a b k i j r ci cj cr (signedBits (P:ℕ)) (signedBits (C:ℕ))
  have ht':(CoefficientTerm.on termMap kind).Executes g (prefixState kind left right a b k i j r ci cj cr) mid t:=by
    convert ht using 1;funext q;fin_cases q <;> rfl
  obtain ⟨u,hu,hub⟩:=Operation.add.executes g (P:ℤ) (C:ℤ) trivial
  have hu':add.Executes g mid (state left right a b k i j r ci cj cr (signedBits (Q:ℕ)) []) u:=by
    have hh:=rename_binary_executes Operation.add.program addMap g mid (signedBits (P:ℕ)) (signedBits (C:ℕ))
      (signedBits (Operation.add.eval (P:ℤ) (C:ℤ))) u hu (by funext q;fin_cases q <;> rfl)
    have he:Operation.add.eval (P:ℤ) (C:ℤ)=(Q:ℤ):=by simp only [Operation.eval,←Nat.cast_add,hPQ]
    rw [he] at hh
    convert hh using 1;funext q;fin_cases q <;> rfl
  have hp:(push (8:Fin 36) true).Executes g (state left right a b k i j r ci cj cr (signedBits (Q:ℕ)) [])
      (prefixState kind left right a b k i j (r+1) ci cj cr) 1:=by
    convert push_executes g (8:Fin 36) true (state left right a b k i j r ci cj cr (signedBits (Q:ℕ)) []) using 1
    funext q;fin_cases q <;> rfl
  refine ⟨_,seq_executes _ _ g ht' (seq_executes _ _ g hu' hp),?_⟩
  have hP: (signedBits (P:ℕ)).length≤ wordBound (inputSize n left right):=
    prefix_word_bound n kind a b left right k i j r ha hb hi hj (by omega)
  have hC:C≤ 2^(entryExponent (inputSize n left right)):=by
    have hQ:=prefix_bound n kind a b left right k i j (r+1) ha hb hi hj (by omega)
    change Q≤ _ at hQ;omega
  have hCW:(signedBits (C:ℕ)).length≤ wordBound (inputSize n left right):=signedBits_length_of_abs_bound hC
  have hm:=polynomial_nat_eval_mono operationTime (show (signedBits (P:ℕ)).length+(signedBits (C:ℕ)).length≤ 2*wordBound (inputSize n left right) by omega)
  dsimp only at hm
  simp only [cellTime,eval_add,eval_comp,eval_mul,eval_X,eval_ofNat,eval_pow,wordBound_eq]
  rw [wordBound_eq] at hm
  omega
lemma cell_queryFree (kind : Kind) : (cell kind).QueryFree:=seq_queryFree _ _ (CoefficientTerm.on_queryFree _ _)
  (seq_queryFree _ _ (rename_queryFree _ _ Operation.add.queryFree) (push_queryFree _ _))
end HiddenCircuits.DH.Runtime.CoefficientEntry
