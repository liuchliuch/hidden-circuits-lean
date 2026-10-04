import HiddenCircuits.DH.Runtime.CoefficientRowRuntime
import HiddenCircuits.DH.Runtime.NumericEncodingUpdate

/-! Fixed46-port ordinary update: four dynamic reads,
one complete coefficient-row loop, three dynamic writes, and real cleanup. -/
namespace HiddenCircuits.DH.Runtime.NumericUpdate
open Complexity Complexity.OracleBlock PruningModel Polynomial
set_option maxHeartbeats 2000000

def state (n keep removed : ℕ) (live sizes table left right a b row sum mark : BitString) : Store 45:=fun q=>
  if q.val=0 then List.replicate keep true else if q.val=1 then List.replicate removed true
  else if q.val=2 then live else if q.val=3 then sizes else if q.val=4 then table
  else if q.val=5 then List.replicate n true else if q.val=6 then left else if q.val=7 then right
  else if q.val=8 then a else if q.val=9 then b else if q.val=10 then row else if q.val=11 then sum
  else if q.val=12 then mark else []
def store (n keep removed : ℕ) (live sizes table : BitString) : Store 45:=
  state n keep removed live sizes table [] [] [] [] [] [] []
def leftMap : Fin 8↪Fin 46:=⟨fun q=>![4,0,6,13,14,15,16,17] q,by decide +kernel⟩
def rightMap : Fin 8↪Fin 46:=⟨fun q=>![4,1,7,13,14,15,16,17] q,by decide +kernel⟩
def sizeLeftMap : Fin 8↪Fin 46:=⟨fun q=>![3,0,8,13,14,15,16,17] q,by decide +kernel⟩
def sizeRightMap : Fin 8↪Fin 46:=⟨fun q=>![3,1,9,13,14,15,16,17] q,by decide +kernel⟩
def rowMap : Fin 39↪Fin 46 where
  toFun q:=⟨if q.val=0 then 5 else if q.val=1 then 8 else if q.val=2 then 9 else if q.val=3 then 6
    else if q.val=4 then 7 else if q.val=5 then 10 else q.val+7,by split_ifs <;> omega⟩
  inj':=by
    intro q z h;apply Fin.ext;have hh:=congrArg Fin.val h
    dsimp only at hh
    split_ifs at hh <;> omega
def tableMap : Fin 8↪Fin 46:=⟨fun q=>![4,0,10,13,14,15,16,17] q,by decide +kernel⟩
def sizesMap : Fin 8↪Fin 46:=⟨fun q=>![3,0,11,13,14,15,16,17] q,by decide +kernel⟩
def liveMap : Fin 8↪Fin 46:=⟨fun q=>![2,1,12,13,14,15,16,17] q,by decide +kernel⟩
noncomputable def reads : OracleBlock 45:=seq (WordArray.readOn leftMap) (seq (WordArray.readOn rightMap)
  (seq (WordArray.readOn sizeLeftMap) (WordArray.readOn sizeRightMap)))
noncomputable def sumSizes : OracleBlock 45:=seq (copyOn 8 11 13 (by decide) (by decide) (by decide))
  (copyOn 9 11 13 (by decide) (by decide) (by decide))
noncomputable def writes : OracleBlock 45:=seq (WordArray.updateOn tableMap) (seq (WordArray.updateOn sizesMap) (WordArray.updateOn liveMap))
noncomputable def core (kind : Kind) : OracleBlock 45:=seq reads (seq (CoefficientRowRuntime.on rowMap kind)
  (seq (seq sumSizes (push 12 false)) writes))
def workPorts : List (Fin 46):=(List.finRange 46).filter (fun q=>6≤ q.val)
noncomputable def program (kind : Kind) : OracleBlock 45:=seq (core kind) (clearList workPorts)
noncomputable def basePolynomial : Polynomial ℕ:=1000*(X+1)^4
noncomputable def envelope : Polynomial ℕ:=basePolynomial+CoefficientRowRuntime.time.comp (3*basePolynomial)+1
noncomputable def time : Polynomial ℕ:=1000000*envelope^3

lemma reads_queryFree : reads.QueryFree:=seq_queryFree _ _ (WordArray.readOn_queryFree _)
  (seq_queryFree _ _ (WordArray.readOn_queryFree _) (seq_queryFree _ _ (WordArray.readOn_queryFree _) (WordArray.readOn_queryFree _)))
lemma writes_queryFree : writes.QueryFree:=seq_queryFree _ _ (WordArray.updateOn_queryFree _)
  (seq_queryFree _ _ (WordArray.updateOn_queryFree _) (WordArray.updateOn_queryFree _))
lemma core_queryFree (kind : Kind) : (core kind).QueryFree:=seq_queryFree _ _ reads_queryFree
  (seq_queryFree _ _ (CoefficientRowRuntime.on_queryFree _ _) (seq_queryFree _ _
    (seq_queryFree _ _ (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (copyOn_queryFree _ _ _ _ _ _))
      (push_queryFree _ _)) writes_queryFree))
lemma queryFree (kind : Kind) : (program kind).QueryFree:=seq_queryFree _ _ (core_queryFree kind) (clearList_queryFree _)
end HiddenCircuits.DH.Runtime.NumericUpdate
