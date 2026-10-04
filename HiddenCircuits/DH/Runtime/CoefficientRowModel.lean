import HiddenCircuits.DH.Runtime.UniformCoefficientModel
import HiddenCircuits.DH.Runtime.NumericEncoding

/-! The physical row updater fills a fixed-length
zero array in increasing index order; this is its exact semantic prefix. -/
namespace HiddenCircuits.DH.Runtime.CoefficientRowRuntime
open Complexity Complexity.BinaryArithmetic PruningModel CoefficientModel
open UniformCoefficientModel

def rowPrefix (n : ℕ) (kind : Kind) (a b : ℕ) (left right : List ℕ) (t : ℕ) : List ℕ:=
  List.ofFn (fun k:Fin (n+1)=>if k.val<t then entry kind a b left right k.val else 0)
def row (n : ℕ) (kind : Kind) (a b : ℕ) (left right : List ℕ) : List ℕ:=
  List.ofFn (fun k:Fin (n+1)=>entry kind a b left right k.val)
lemma rowPrefix_length (n : ℕ) (kind : Kind) (a b : ℕ) (left right : List ℕ) (t : ℕ) :
    (rowPrefix n kind a b left right t).length=n+1:=by simp [rowPrefix]
lemma rowPrefix_zero (n : ℕ) (kind : Kind) (a b : ℕ) (left right : List ℕ) :
    rowPrefix n kind a b left right 0=List.replicate (n+1) 0:=by simp only [rowPrefix,Nat.not_lt_zero,if_false,List.ofFn_const]
lemma rowPrefix_step (n : ℕ) (kind : Kind) (a b : ℕ) (left right : List ℕ) (t : ℕ) (ht:t≤ n) :
    (rowPrefix n kind a b left right t).set t (entry kind a b left right t)=rowPrefix n kind a b left right (t+1):=by
  apply List.ext_getElem
  · simp [rowPrefix]
  · intro j hj hj'
    simp only [List.getElem_set,rowPrefix,List.getElem_ofFn]
    by_cases he:t=j
    · subst j;simp
    · have hje:¬j=t:=Ne.symm he
      simp only [he,if_false]
      change (if j<t then _ else 0)=(if j<t+1 then _ else 0)
      by_cases hlt:j<t
      · simp [hlt,show j<t+1 by omega]
      · simp [hlt,show ¬j<t+1 by omega]
lemma rowPrefix_complete (n : ℕ) (kind : Kind) (a b : ℕ) (left right : List ℕ) :
    rowPrefix n kind a b left right (n+1)=row n kind a b left right:=by
  simp [rowPrefix,row]
lemma row_eq_mergeRow (n : ℕ) (kind : Kind) (a b : ℕ) (left right : List ℕ)
    (hl:∀i,a < i → CoefficientModel.read left i=0) (hr:∀j,b < j → CoefficientModel.read right j=0) :
    row n kind a b left right=mergeRow n kind a b left right:=by
  simp only [row,mergeRow,entry_eq_mergeEntry kind a b left right _ hl hr]
lemma rowPrefix_bound (n : ℕ) (kind : Kind) (a b : ℕ) (left right : List ℕ) (t k : ℕ)
    (ha:a≤ n) (hb:b≤ n) :
    CoefficientModel.read (rowPrefix n kind a b left right t) k≤ 2^(CoefficientRow.entryExponent (CoefficientRow.inputSize n left right)):=by
  by_cases hk:k<n+1
  · simp only [CoefficientModel.read,rowPrefix,List.getElem?_ofFn,hk,↓reduceDIte,Option.getD_some]
    split_ifs
    · exact entry_bound n kind a b left right k ha hb
    · exact Nat.zero_le _
  · simp [CoefficientModel.read,rowPrefix,hk]
lemma rowPrefix_bits_bound (n : ℕ) (kind : Kind) (a b : ℕ) (left right : List ℕ) (t : ℕ)
    (ha:a≤ n) (hb:b≤ n) :
    (NumericEncoding.rowBits (rowPrefix n kind a b left right t)).length≤
      2*(n+1)*(CoefficientRow.entryExponent (CoefficientRow.inputSize n left right)+3):=
  NumericEncoding.rowBits_bound _ n _ (rowPrefix_length ..) (fun k=>rowPrefix_bound n kind a b left right t k ha hb)
end HiddenCircuits.DH.Runtime.CoefficientRowRuntime
