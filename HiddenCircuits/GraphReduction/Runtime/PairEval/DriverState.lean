import HiddenCircuits.Complexity.PairEncoding
import HiddenCircuits.GraphReduction.Runtime.WordGraph.RecoveryBounds
import HiddenCircuits.GraphReduction.Runtime.WordGraph.ComplementFor

/-! Standalone PairEval physical interpolation store. -/
namespace HiddenCircuits.GraphReduction.Runtime.PairEval.Driver
open Complexity OracleBlock BinaryArithmetic

def degree (w : PairInput) : ℕ := 2*w.particles*w.pairs.length

def state (w : PairInput) (l s : ℕ) (a : ℤ×ℤ) (answer num den : BitString) : Store 97 := fun i =>
  if i.val=0 then pairInputBits w else if i.val=1 then List.replicate w.particles true
  else if i.val=2 then List.replicate w.pairs.length true else if i.val=3 then List.replicate (2*w.particles) true
  else if i.val=4 then List.replicate (degree w) true else if i.val=5 then List.replicate l true
  else if i.val=6 then List.replicate s true
  else if i.val=10 then signedBits a.1 else if i.val=11 then signedBits a.2
  else if i.val=12 then answer else if i.val=13 then num else if i.val=14 then den else []

lemma state_update_inner (w : PairInput) (l s l' : ℕ) (a : ℤ×ℤ) (answer num den : BitString) :
    Function.update (state w l s a answer num den) (5:Fin 98) (List.replicate l' true)=
      state w l' s a answer num den := by
  funext i;by_cases hi:i=5
  · subst i;rfl
  · simp only [Function.update_of_ne hi,state]
    have hn : i.val≠5 := fun he => hi (Fin.ext he)
    simp only [hn,if_false]
lemma state_update_s (w : PairInput) (l s s' : ℕ) (a : ℤ×ℤ) (answer num den : BitString) :
    Function.update (state w l s a answer num den) (6:Fin 98) (List.replicate s' true)=
      state w l s' a answer num den := by
  funext i;by_cases hi:i=6
  · subst i;rfl
  · simp only [Function.update_of_ne hi,state]
    have hn : i.val≠6 := fun he => hi (Fin.ext he)
    simp only [hn,if_false]
end HiddenCircuits.GraphReduction.Runtime.PairEval.Driver
