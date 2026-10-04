import HiddenCircuits.Circuit.Runtime.SpectralDenominator
import HiddenCircuits.Circuit.GeometricIntegerWeights

/-! Compute a geometric zero-evaluation weight using two
actual integer product routines, preserving the distinguished node and roots. -/
namespace HiddenCircuits.Circuit.Runtime.GeometricWeights
open HiddenCircuits.Complexity OracleBlock BinaryArithmetic Polynomial IntegerSpectralWeights LagrangeIntegerArrays

def store (x roots num den work : BitString) : Store 22 := fun i =>
  if i.val=0 then x else if i.val=1 then roots else if i.val=2 then num else if i.val=3 then den
  else if i.val=4 then work else []
def denominatorEmbedding : Fin 19 ↪ Fin 23 where
  toFun i := ⟨i.val+3,by omega⟩
  inj' := by intro i j h;apply Fin.ext;have hh:=congrArg Fin.val h;dsimp at hh;omega
def numeratorEmbedding : Fin 19 ↪ Fin 23 where
  toFun i := if i.val=0 then 2 else ⟨i.val+3,by omega⟩
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
noncomputable def prepare : OracleBlock 22 := seq (copyOn 0 3 22 (by decide) (by decide) (by decide))
  (copyOn 1 4 22 (by decide) (by decide) (by decide))
noncomputable def zeroPrepare : OracleBlock 22 := seq (push 2 false) (copyOn 1 4 22 (by decide) (by decide) (by decide))
noncomputable def program : OracleBlock 22 := seq prepare
  (seq (SpectralDenominator.programOn denominatorEmbedding) (seq zeroPrepare (SpectralDenominator.programOn numeratorEmbedding)))
noncomputable def time : Polynomial ℕ := 2*SpectralDenominator.time.comp (X+1)+10*X+17

def inputLength (x : ℤ) (xs : List ℤ) : ℕ := SpectralDenominator.inputLength x xs

lemma prepare_executes (g : BitString → ℕ) (x roots : BitString) :
    prepare.Executes g (store x roots [] [] []) (store x roots [] x roots) (5*x.length+5*roots.length+6) := by
  have hx : (copyOn (0:Fin 23) 3 22 (by decide) (by decide) (by decide)).Executes g
      (store x roots [] [] []) (store x roots [] x []) (5*x.length+2) := by
    convert copyOn_executes g (0:Fin 23) 3 22 (by decide) (by decide) (by decide) (store x roots [] [] []) rfl using 1
    funext i;fin_cases i <;> simp [store]
  have hr : (copyOn (1:Fin 23) 4 22 (by decide) (by decide) (by decide)).Executes g
      (store x roots [] x []) (store x roots [] x roots) (5*roots.length+2) := by
    convert copyOn_executes g (1:Fin 23) 4 22 (by decide) (by decide) (by decide) (store x roots [] x []) rfl using 1
    funext i;fin_cases i <;> simp [store]
  convert seq_executes _ _ g hx hr using 1 <;> omega

lemma zeroPrepare_executes (g : BitString → ℕ) (x roots den : BitString) :
    zeroPrepare.Executes g (store x roots [] den []) (store x roots (signedBits 0) den roots) (5*roots.length+5) := by
  have hz : (push (2:Fin 23) false).Executes g (store x roots [] den []) (store x roots (signedBits 0) den []) 1 := by
    convert push_executes g (2:Fin 23) false (store x roots [] den []) using 1
    funext i;fin_cases i <;> rfl
  have hr : (copyOn (1:Fin 23) 4 22 (by decide) (by decide) (by decide)).Executes g
      (store x roots (signedBits 0) den []) (store x roots (signedBits 0) den roots) (5*roots.length+2) := by
    convert copyOn_executes g (1:Fin 23) 4 22 (by decide) (by decide) (by decide) (store x roots (signedBits 0) den []) rfl using 1
    funext i;fin_cases i <;> simp [store]
  convert seq_executes _ _ g hz hr using 1 <;> omega

set_option maxHeartbeats 600000 in
theorem program_executes (g : BitString → ℕ) (x : ℤ) (xs : List ℤ) :
    ∃c,program.Executes g (store (signedBits x) (encodeBitList (xs.map signedBits)) [] [] [])
      (store (signedBits x) (encodeBitList (xs.map signedBits)) (signedBits (denominator 0 xs))
        (signedBits (denominator x xs)) []) c ∧ c≤ time.eval (inputLength x xs) := by
  let roots := encodeBitList (xs.map signedBits)
  have hp:=prepare_executes g (signedBits x) roots
  obtain ⟨a,ha,hab⟩:=SpectralDenominator.programOn_executes denominatorEmbedding g
    (store (signedBits x) roots [] (signedBits x) roots) x xs (by funext i;fin_cases i <;> rfl)
  have hea : Function.update (Function.update (store (signedBits x) roots [] (signedBits x) roots)
      (denominatorEmbedding 0) (signedBits (denominator x xs))) (denominatorEmbedding 1) []=
      store (signedBits x) roots [] (signedBits (denominator x xs)) [] := by funext i;fin_cases i <;> rfl
  rw [hea] at ha
  have hz:=zeroPrepare_executes g (signedBits x) roots (signedBits (denominator x xs))
  obtain ⟨b,hb,hbb⟩:=SpectralDenominator.programOn_executes numeratorEmbedding g
    (store (signedBits x) roots (signedBits 0) (signedBits (denominator x xs)) roots) 0 xs (by funext i;fin_cases i <;> rfl)
  have heb : Function.update (Function.update (store (signedBits x) roots (signedBits 0) (signedBits (denominator x xs)) roots)
      (numeratorEmbedding 0) (signedBits (denominator 0 xs))) (numeratorEmbedding 1) []=
      store (signedBits x) roots (signedBits (denominator 0 xs)) (signedBits (denominator x xs)) [] := by funext i;fin_cases i <;> rfl
  rw [heb] at hb
  refine ⟨_,seq_executes _ _ g hp (seq_executes _ _ g ha (seq_executes _ _ g hz hb)),?_⟩
  have hA:=polynomial_nat_eval_mono SpectralDenominator.time (show inputLength x xs≤ inputLength x xs+1 by omega)
  have hB:=polynomial_nat_eval_mono SpectralDenominator.time (show SpectralDenominator.inputLength 0 xs≤ inputLength x xs+1 by
    change 1+(encodeBitList (xs.map signedBits)).length≤(signedBits x).length+(encodeBitList (xs.map signedBits)).length+1
    omega)
  dsimp only at hA hB
  simp only [time,eval_add,eval_mul,eval_comp,eval_X,eval_ofNat,eval_one]
  dsimp only [inputLength,SpectralDenominator.inputLength,roots] at *
  omega

lemma zero_denominator_coeff (xs : List ℤ) : denominator 0 xs=coeffs xs 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (0-x)*denominator 0 xs = -x*IntegerSpectralWeights.coeffs xs 0
    rw [ih,zero_sub]
lemma geometric_numerator (d : ℕ) (i : Fin (d+1)) :
    denominator 0 (otherNodes (List.finRange (d+1)) geometricIntegerNode i)=geometricZeroNumerator d i := by
  rw [geometricZeroNumerator,arrayRun_read,zero_denominator_coeff]

lemma program_queryFree : program.QueryFree := seq_queryFree _ _
  (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (copyOn_queryFree _ _ _ _ _ _))
  (seq_queryFree _ _ (SpectralDenominator.programOn_queryFree _) (seq_queryFree _ _
    (seq_queryFree _ _ (push_queryFree _ _) (copyOn_queryFree _ _ _ _ _ _)) (SpectralDenominator.programOn_queryFree _)))
noncomputable def on {k : ℕ} (φ : Fin 23 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 23 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k) (x : ℤ) (xs : List ℤ)
    (hs : s∘φ=store (signedBits x) (encodeBitList (xs.map signedBits)) [] [] []) :
    ∃c,(on φ).Executes g s (Function.update (Function.update s (φ 2) (signedBits (denominator 0 xs)))
      (φ 3) (signedBits (denominator x xs))) c ∧ c≤ time.eval (inputLength x xs) := by
  obtain ⟨c,hc,hb⟩:=program_executes g x xs
  refine ⟨c,?_,hb⟩
  apply rename_executes_to _ φ g hc hs
  · funext i
    have hi:=congrFun hs i
    change s (φ i)=_ at hi
    simp only [Function.comp_def,Function.update_apply,φ.injective.eq_iff,hi]
    fin_cases i <;> rfl
  · intro i hi;simp only [Function.update_of_ne (hi 2).symm,Function.update_of_ne (hi 3).symm]
lemma on_queryFree {k : ℕ} (φ : Fin 23 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ program_queryFree
end HiddenCircuits.Circuit.Runtime.GeometricWeights
