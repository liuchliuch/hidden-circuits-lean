import HiddenCircuits.Complexity.CNFSerialization
import HiddenCircuits.Complexity.OracleRepeat

namespace HiddenCircuits.Complexity.CNFCloneEmitter.LiteralWord
open OracleBlock

def store (index counter temporary output : BitString) : Store 3 := fun i =>
  if i.val=0 then index else if i.val=1 then counter else if i.val=2 then temporary else output

noncomputable def program (sign : Bool) : OracleBlock 3 :=
  seq (copyOn 0 1 2 (by decide) (by decide) (by decide))
    (seq (prepend 3 [false,sign]) (repeatPrepend 1 3 [true,true]))

lemma pair_unary (i : ℕ) (rest : BitString) :
    pairBits (List.replicate i true) rest=List.replicate (2*i) true++false::rest := by
  rw [pairBits_escape,escapeBits_replicate_true]

theorem program_executes (g : BitString → ℕ) (i : ℕ) (sign : Bool) :
    (program sign).Executes g (store (List.replicate i true) [] [] [])
      (store (List.replicate i true) [] [] (pairBits (List.replicate i true) [sign])) (14*i+14) := by
  have hc : (copyOn (0 : Fin 4) 1 2 (by decide) (by decide) (by decide)).Executes g
      (store (List.replicate i true) [] [] []) (store (List.replicate i true) (List.replicate i true) [] []) (5*i+2) := by
    convert copyOn_executes g (0 : Fin 4) 1 2 (by decide) (by decide) (by decide)
      (store (List.replicate i true) [] [] []) rfl using 1
    · funext j;fin_cases j <;> simp [store]
    · simp [store]
  have hp : (prepend (3 : Fin 4) [false,sign]).Executes g
      (store (List.replicate i true) (List.replicate i true) [] [])
      (store (List.replicate i true) (List.replicate i true) [] [false,sign]) 7 := by
    convert prepend_executes g (3 : Fin 4) [false,sign]
      (store (List.replicate i true) (List.replicate i true) [] []) using 1
    funext j;fin_cases j <;> simp [store]
  have hr : (repeatPrepend (1 : Fin 4) 3 [true,true]).Executes g
      (store (List.replicate i true) (List.replicate i true) [] [false,sign])
      (store (List.replicate i true) [] [] (pairBits (List.replicate i true) [sign])) (9*i+1) := by
    have h := repeatPrepend_executes g (1 : Fin 4) 3 (by decide) [true,true]
      (store (List.replicate i true) (List.replicate i true) [] [false,sign])
    rw [show [true,true]=List.replicate 2 true from rfl] at h
    have hrep : (List.replicate i [true,true]).flatten=List.replicate (2*i) true := by
      change (List.replicate i (List.replicate 2 true)).flatten=List.replicate (2*i) true
      simp only [List.flatten_replicate_replicate,Nat.mul_comm]
    convert h using 1
    · funext j;fin_cases j <;> simp [store,pair_unary,hrep]
    · simp [store]
  convert seq_executes _ _ g hc (seq_executes _ _ g hp hr) using 1 <;> omega

lemma program_queryFree (sign : Bool) : (program sign).QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (prepend_queryFree _ _) (repeatPrepend_queryFree _ _ _))

end HiddenCircuits.Complexity.CNFCloneEmitter.LiteralWord
