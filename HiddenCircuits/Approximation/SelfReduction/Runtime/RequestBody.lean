import HiddenCircuits.Approximation.SelfReduction.Runtime.CoinBlocks
import HiddenCircuits.Approximation.SelfReduction.Runtime.WordEmit

/-! Actual preparation of one sampler request from fresh fixed-width coin bits. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

def requestStore (coins context out : BitString) (width count : ℕ) (clock chunk copy : BitString) : Store 10 := fun i =>
  if i.val=0 then coins else if i.val=1 then context else if i.val=2 then List.replicate width true
  else if i.val=3 then List.replicate count true else if i.val=4 then out else if i.val=5 then clock
  else if i.val=6 then chunk else if i.val=8 then copy else []

def requestTakeEmbedding : Fin 4 ↪ Fin 11 where
  toFun i := if i.val=0 then 0 else if i.val=1 then 5 else if i.val=2 then 6 else 7
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

noncomputable def requestTake : OracleBlock 10 := rename takeCoins requestTakeEmbedding
noncomputable def requestBody : OracleBlock 10 :=
  seq (copyOn 2 5 10 (by decide) (by decide) (by decide))
    (seq requestTake (seq (copyOn 1 8 10 (by decide) (by decide) (by decide))
      (seq (pairEmit 8 6 9 (by decide) (by decide)) (emitWordReversed 6 4))))

/-- Every request copies its real context and consumes exactly one disjoint
coin block. The original width/context and untouched random suffix are preserved. -/
theorem requestBody_executes (g : BitString → ℕ) (bits rest context out : BitString)
    (width count : ℕ) (hwidth : bits.length=width) :
    requestBody.Executes g (requestStore (bits++rest) context out width count [] [] [])
      (requestStore rest context ((true::pairBits (pairBits context bits) []).reverse ++ out) width count [] [] [])
      (18*width+25*context.length+36) := by
  have h1 : (copyOn (2 : Fin 11) 5 10 (by decide) (by decide) (by decide)).Executes g
      (requestStore (bits++rest) context out width count [] [] [])
      (requestStore (bits++rest) context out width count (List.replicate width true) [] []) (5*width+2) := by
    convert copyOn_executes g (2 : Fin 11) 5 10 (by decide) (by decide) (by decide)
      (requestStore (bits++rest) context out width count [] [] []) rfl using 1
    · funext i; fin_cases i <;> simp [requestStore]
    · simp [requestStore]
  have h2 : requestTake.Executes g
      (requestStore (bits++rest) context out width count (List.replicate width true) [] [])
      (requestStore rest context out width count [] bits []) (7*width+4) := by
    have h := takeCoins_executes g bits rest
    rw [hwidth] at h
    apply rename_executes_to takeCoins requestTakeEmbedding g h
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
    · intro j hj; fin_cases j
      all_goals first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) | exact False.elim (hj 2 rfl) | exact False.elim (hj 3 rfl)
  have h3 : (copyOn (1 : Fin 11) 8 10 (by decide) (by decide) (by decide)).Executes g
      (requestStore rest context out width count [] bits [])
      (requestStore rest context out width count [] bits context) (5*context.length+2) := by
    convert copyOn_executes g (1 : Fin 11) 8 10 (by decide) (by decide) (by decide)
      (requestStore rest context out width count [] bits []) rfl using 1
    funext i; fin_cases i <;> simp [requestStore]
  have h4 : (pairEmit (8 : Fin 11) 6 9 (by decide) (by decide)).Executes g
      (requestStore rest context out width count [] bits context)
      (requestStore rest context out width count [] (pairBits context bits) []) (8*context.length+7) := by
    convert pairEmit_executes g (8 : Fin 11) 6 9 (by decide) (by decide) (by decide)
      (requestStore rest context out width count [] bits context) rfl using 1
    funext i; fin_cases i <;> simp [requestStore]
  have h5 : (emitWordReversed (6 : Fin 11) 4).Executes g
      (requestStore rest context out width count [] (pairBits context bits) [])
      (requestStore rest context ((true::pairBits (pairBits context bits) []).reverse ++ out) width count [] [] [])
      (6*(2*context.length+width+1)+7) := by
    convert emitWordReversed_executes g (6 : Fin 11) 4 (by decide)
      (requestStore rest context out width count [] (pairBits context bits) []) using 1
    · funext i; fin_cases i <;> simp [requestStore]
    · simp [requestStore,hwidth]
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 (seq_executes _ _ g h4 h5))) using 1 <;> omega

end HiddenCircuits.Approximation.SelfReduction.Runtime
