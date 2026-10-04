import HiddenCircuits.Circuit.Runtime.ConstraintSourceQuery
import HiddenCircuits.Circuit.Runtime.DyadicScalar
import HiddenCircuits.Complexity.FinalCountRuntime

namespace HiddenCircuits.Circuit.Runtime.ConstraintSource
open Complexity OracleBlock BinaryArithmetic Polynomial
set_option maxHeartbeats 1200000

def finishStore (raw : BitString) (a n f z : ℕ) (num den flag unit : BitString := []) : Store 35 := fun i=>
  if i.val=0 then raw else if i.val=1 then List.replicate a true else if i.val=2 then List.replicate n true
  else if i.val=3 then List.replicate f true else if i.val=4 then List.replicate z true
  else if i.val=11 then num else if i.val=12 then den else if i.val=19 then flag else if i.val=20 then unit else []
def parseMap : Fin 4 ↪ Fin 36 := ⟨fun i=>![0,11,24,25] i,by decide +kernel⟩
def dyadicMap : Fin 7 ↪ Fin 36 := ⟨fun i=>![1,18,19,12,20,24,25] i,by decide +kernel⟩
def divideMap : Fin 9 ↪ Fin 36 := ⟨fun i=>![11,12,24,25,26,27,28,29,30] i,by decide +kernel⟩
noncomputable def denominator : OracleBlock 35 := seq (SamplePairParser.on parseMap)
  (seq (clear 0) (seq (push 19 false) (DyadicScalar.on dyadicMap)))
noncomputable def divide : OracleBlock 35 := rename FinalCountRuntime.program divideMap
noncomputable def quotient : OracleBlock 35 := seq denominator divide
noncomputable def finish : OracleBlock 35 := seq quotient (cleanResult 11 24 (by decide) (by decide))
noncomputable def denominatorTime : Polynomial ℕ := 25*X+57
noncomputable def quotientTime : Polynomial ℕ := denominatorTime+FinalCountRuntime.time.comp (2*(X+denominatorTime))+2
noncomputable def finishTime : Polynomial ℕ := quotientTime+40*(X+quotientTime+3)+3

lemma initial_finishStore (raw : BitString) (a n f z : ℕ) : finishStore raw a n f z=SourceMetadata.outputStore raw a n f z := by
  funext i;fin_cases i <;> rfl
lemma denominator_executes (g : BitString→ℕ) (a n f z : ℕ) (u : ℤ) :
    ∃c,denominator.Executes g (finishStore (pairBits (signedBits u) (signedBits 1)) a n f z)
      (finishStore [] a n f z (signedBits u) (signedBits ((2:ℤ)^(3*a))) [false] (signedBits 1)) c ∧
      c ≤ 5*(signedBits u).length+20*a+57 := by
  have hp : (SamplePairParser.on parseMap).Executes g
      (finishStore (pairBits (signedBits u) (signedBits 1)) a n f z)
      (finishStore (signedBits 1) a n f z (signedBits u)) (5*(signedBits u).length+7) := by
    apply SamplePairParser.on_executes parseMap g (signedBits u) (signedBits 1)
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | (exfalso;exact hi 0 rfl) | (exfalso;exact hi 1 rfl)
  have hc : (clear (0:Fin 36)).Executes g (finishStore (signedBits 1) a n f z (signedBits u))
      (finishStore [] a n f z (signedBits u)) 3 := by
    convert clear_executes g (0:Fin 36) (finishStore (signedBits 1) a n f z (signedBits u)) using 1
    funext i;fin_cases i <;> rfl
  have hf : (push (19:Fin 36) false).Executes g (finishStore [] a n f z (signedBits u))
      (finishStore [] a n f z (signedBits u) [] [false]) 1 := by
    convert push_executes g (19:Fin 36) false (finishStore [] a n f z (signedBits u)) using 1
    funext i;fin_cases i <;> rfl
  obtain ⟨c,hd,hb⟩:=DyadicScalar.on_executes dyadicMap g (finishStore [] a n f z (signedBits u) [] [false]) a 0 false
    (by funext i;fin_cases i <;> rfl)
  have hd' : (DyadicScalar.on dyadicMap).Executes g (finishStore [] a n f z (signedBits u) [] [false])
      (finishStore [] a n f z (signedBits u) (signedBits ((2:ℤ)^(3*a))) [false] (signedBits 1)) c := by
    convert hd using 1
    funext i;fin_cases i <;> simp [finishStore,dyadicMap,DyadicScalar.numerator]
  refine ⟨5*(signedBits u).length+7+(3+(1+c+2)+2)+2,seq_executes _ _ g hp (seq_executes _ _ g hc (seq_executes _ _ g hf hd')),?_⟩
  simp only [DyadicScalar.time,eval_add,eval_mul,eval_X,eval_ofNat,Nat.add_zero] at hb
  omega

lemma divide_executes (g : BitString→ℕ) (a n f z count : ℕ) (u : ℤ) (hu : u=(count:ℤ)*(2:ℤ)^(3*a)) :
    ∃c,divide.Executes g (finishStore [] a n f z (signedBits u) (signedBits ((2:ℤ)^(3*a))) [false] (signedBits 1))
      (finishStore [] a n f z (Computability.encodeNat count) [] [false] (signedBits 1)) c ∧
      c ≤ FinalCountRuntime.time.eval ((signedBits u).length+(signedBits ((2:ℤ)^(3*a))).length) := by
  obtain ⟨c,hc,hb⟩:=FinalCountRuntime.program_executes g u ((2:ℤ)^(3*a)) count (pow_ne_zero _ (by norm_num)) hu
  refine ⟨c,?_,hb⟩
  apply rename_executes_to _ divideMap g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | (exfalso;exact hi 0 rfl) | (exfalso;exact hi 1 rfl)
end HiddenCircuits.Circuit.Runtime.ConstraintSource
