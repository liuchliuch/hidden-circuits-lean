import HiddenCircuits.Complexity.PolynomialBounds
import HiddenCircuits.Approximation.SelfReduction.Runtime.MapLoop
import HiddenCircuits.Complexity.BinaryArithmetic.UnaryBinary
import HiddenCircuits.Complexity.BinaryArithmetic.AccumulatorRuntime

/-! Literal unary-to-signed-binary conversion and its clean list map. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.EstimateOutput
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic Polynomial

def clean {k : ℕ} (word : BitString) : Store k := Function.update (fun _ => []) 0 word

@[simp] theorem clean_zero {k : ℕ} (word : BitString) : clean (k:=k) word 0=word := by simp [clean]

 theorem natBits_length (n : ℕ) : (Computability.encodeNat n).length≤n := by
  rw [encodeNat_length]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

@[simp] theorem signedBits_nat (n : ℕ) : signedBits (n : ℤ)=false::Computability.encodeNat n := by
  simp [signedBits,negative]

noncomputable def unarySigned : OracleBlock 2 := seq unaryBinary
  (seq (moveOn 1 0 2 (by decide) (by decide) (by decide)) (push 0 false))
noncomputable def unaryTime : Polynomial ℕ := 4*X^2+11*X+11

 theorem unarySigned_executes (g : BitString → ℕ) (word : BitString) :
    ∃ t, unarySigned.Executes g (clean word) (clean (signedBits (word.length : ℤ))) t ∧
      t≤unaryTime.eval word.length := by
  let s1 := unaryBinaryStore [] (Computability.encodeNat word.length) []
  have hu : unaryBinary.Executes g (clean word) s1 (unaryBinaryCost 0 word.length) := by
    convert unaryBinary_executes g word 0 using 1
    · funext i; fin_cases i <;> rfl
    · simp [s1]
  have hm : (moveOn (1:Fin 3) 0 2 (by decide) (by decide) (by decide)).Executes g s1
      (clean (Computability.encodeNat word.length)) (6*(Computability.encodeNat word.length).length+5) := by
    convert moveOn_executes g (1:Fin 3) 0 2 (by decide) (by decide) (by decide) s1 rfl using 1
    funext i; fin_cases i <;> simp [s1,clean,unaryBinaryStore]
  have hp : (push (0:Fin 3) false).Executes g (clean (Computability.encodeNat word.length))
      (clean (signedBits (word.length : ℤ))) 1 := by
    simpa [clean,signedBits_nat] using push_executes g (0:Fin 3) false (clean (Computability.encodeNat word.length))
  refine ⟨_,seq_executes _ _ g hu (seq_executes _ _ g hm hp),?_⟩
  have hb := unaryBinaryCost_le word.length 0 word.length (by omega)
  have hl := natBits_length word.length
  simp only [unaryTime,eval_add,eval_mul,eval_pow,eval_X,eval_ofNat]
  nlinarith

 theorem unarySigned_queryFree : unarySigned.QueryFree := seq_queryFree _ _ unaryBinary_queryFree
  (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _) (push_queryFree _ _))

noncomputable def mapSigned : OracleBlock 6 := mapProgram unarySigned
noncomputable def mapTime : Polynomial ℕ := 6*X+X*(15*X+11*unaryTime+24)+11

def unaryWords (xs : List ℕ) : List BitString := xs.map (fun n => List.replicate n true)
def signedWords (xs : List ℕ) : List BitString := xs.map (fun n : ℕ => signedBits (n : ℤ))

 theorem mapSigned_executes (g : BitString → ℕ) (xs : List ℕ) :
    ∃ t, mapSigned.Executes g (clean (encodeBitList (unaryWords xs)))
      (clean (encodeBitList (signedWords xs))) t ∧
      t≤mapTime.eval (encodeBitList (unaryWords xs)).length := by
  let N := (encodeBitList (unaryWords xs)).length
  have hxs : ∀ word ∈ unaryWords xs, word.length≤N := fun _ h => member_length_le_encodeBitList h
  have hB : ∀ word ∈ unaryWords xs, ∃ t, unarySigned.Executes g (clean word)
      (clean (signedBits (word.length : ℤ))) t ∧ t≤unaryTime.eval N := by
    intro word hw
    obtain ⟨t,ht,hb⟩ := unarySigned_executes g word
    exact ⟨t,ht,hb.trans (polynomial_nat_eval_mono unaryTime (hxs word hw))⟩
  obtain ⟨t,ht,hb⟩ := mapProgram_executes unarySigned (fun word => signedBits (word.length : ℤ)) g
    (unaryWords xs) N (unaryTime.eval N) hxs hB
  have hm : (unaryWords xs).map (fun word => signedBits (word.length : ℤ))=signedWords xs := by
    change (xs.map (fun n => List.replicate n true)).map (fun word => signedBits (word.length : ℤ)) = xs.map (fun n : ℕ => signedBits (n : ℤ))
    simp only [List.map_map,List.length_replicate,Function.comp_def]
  rw [hm] at ht
  refine ⟨t,ht,hb.trans ?_⟩
  have hl := list_length_le_encodeBitList_length (unaryWords xs)
  change (unaryWords xs).length≤N at hl
  simp only [mapTime,eval_add,eval_mul,eval_X,eval_ofNat]
  change 6*N+(unaryWords xs).length*(15*N+11*unaryTime.eval N+24)+11 ≤ _
  exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_right _ hl) _) _

 theorem mapSigned_queryFree : mapSigned.QueryFree := mapProgram_queryFree _ unarySigned_queryFree

end HiddenCircuits.Approximation.SelfReduction.Runtime.EstimateOutput
