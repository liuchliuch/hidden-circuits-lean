import HiddenCircuits.GraphReduction.Runtime.WordGraph.RecoveryBounds
import HiddenCircuits.GraphReduction.Runtime.WordGraph.ComplementFor

/-! Fresh reconstruction of the literal98-stack interpolation store. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.Driver
open Complexity OracleBlock BinaryArithmetic

def state (w : WordInstance) (k t h l s : ℕ) (a : ℤ×ℤ) (answer num den : BitString) : Store 97 := fun i =>
  if i.val=0 then wordBits w else if i.val=1 then List.replicate w.particles true
  else if i.val=2 then List.replicate w.word.length true else if i.val=3 then List.replicate (2*w.particles) true
  else if i.val=4 then List.replicate (Recovery.degree w) true else if i.val=5 then List.replicate k true
  else if i.val=6 then List.replicate t true else if i.val=7 then List.replicate h true
  else if i.val=8 then List.replicate l true else if i.val=9 then List.replicate s true
  else if i.val=10 then signedBits a.1 else if i.val=11 then signedBits a.2
  else if i.val=12 then answer else if i.val=13 then num else if i.val=14 then den else []

lemma state_update_inner (w : WordInstance) (k t h l s l' : ℕ) (a : ℤ×ℤ) (answer num den : BitString) :
    Function.update (state w k t h l s a answer num den) (8:Fin 98) (List.replicate l' true)=
      state w k t h l' s a answer num den := by
  funext i;by_cases hi:i=8
  · subst i;rfl
  · simp only [Function.update_of_ne hi,state]
    have hn : i.val≠8 := fun he => hi (Fin.ext he)
    simp only [hn,if_false]
lemma state_update_s (w : WordInstance) (k t h l s s' : ℕ) (a : ℤ×ℤ) (answer num den : BitString) :
    Function.update (state w k t h l s a answer num den) (9:Fin 98) (List.replicate s' true)=
      state w k t h l s' a answer num den := by
  funext i;by_cases hi:i=9
  · subst i;rfl
  · simp only [Function.update_of_ne hi,state]
    have hn : i.val≠9 := fun he => hi (Fin.ext he)
    simp only [hn,if_false]
lemma state_update_outer (w : WordInstance) (k t h l s k' : ℕ) (a : ℤ×ℤ) (answer num den : BitString) :
    Function.update (state w k t h l s a answer num den) (5:Fin 98) (List.replicate k' true)=
      state w k' t h l s a answer num den := by
  funext i;by_cases hi:i=5
  · subst i;rfl
  · simp only [Function.update_of_ne hi,state]
    have hn : i.val≠5 := fun he => hi (Fin.ext he)
    simp only [hn,if_false]
lemma state_update_t (w : WordInstance) (k t h l s t' : ℕ) (a : ℤ×ℤ) (answer num den : BitString) :
    Function.update (state w k t h l s a answer num den) (6:Fin 98) (List.replicate t' true)=
      state w k t' h l s a answer num den := by
  funext i;by_cases hi:i=6
  · subst i;rfl
  · simp only [Function.update_of_ne hi,state]
    have hn : i.val≠6 := fun he => hi (Fin.ext he)
    simp only [hn,if_false]
end HiddenCircuits.GraphReduction.Runtime.WordGraph.Driver
