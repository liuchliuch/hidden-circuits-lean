import HiddenCircuits.Circuit.Runtime.SpectralCoefficients
import HiddenCircuits.Circuit.Runtime.SpectralDenominator
import HiddenCircuits.Circuit.SpectralIntegerWeights

/-! One real Lagrange-basis computation returns every signed numerator coefficient and its denominator. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralBasis
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic IntegerSpectralWeights Polynomial

/-- Preserved distinguished node0/root stream1, output coefficient stream2 and
signed denominator3; all work positions4–26 are empty in the public interface. -/
def store (x roots numerators denominator left right : BitString) : Store 26 := fun i =>
  if i.val=0 then x else if i.val=1 then roots else if i.val=2 then numerators
  else if i.val=3 then denominator else if i.val=4 then left else if i.val=5 then right else []

def coefficientEmbedding : Fin 23 ↪ Fin 27 where
  toFun i := ⟨i.val+4,by omega⟩
  inj' := by intro i j h;apply Fin.ext;have hh := congrArg (fun z : Fin 27 => z.val) h;change i.val+4=j.val+4 at hh;omega
 def denominatorEmbedding : Fin 19 ↪ Fin 27 where
  toFun i := ⟨i.val+4,by omega⟩
  inj' := by intro i j h;apply Fin.ext;have hh := congrArg (fun z : Fin 27 => z.val) h;change i.val+4=j.val+4 at hh;omega

noncomputable def program : OracleBlock 26 :=
  seq (copyOn 1 4 6 (by decide) (by decide) (by decide))
    (seq (SpectralCoefficients.programOn coefficientEmbedding)
      (seq (moveOn 4 2 6 (by decide) (by decide) (by decide))
        (seq (copyOn 0 4 6 (by decide) (by decide) (by decide))
          (seq (copyOn 1 5 6 (by decide) (by decide) (by decide))
            (seq (SpectralDenominator.programOn denominatorEmbedding)
              (moveOn 4 3 6 (by decide) (by decide) (by decide)))))))

noncomputable def time : Polynomial ℕ := SpectralCoefficients.time+SpectralDenominator.time+
  10*X+6*SpectralCoefficients.coefficientStreamBound+6*SpectralDenominator.registerBound+28

def inputLength (x : ℤ) (xs : List ℤ) : ℕ := (signedBits x).length+(encodeBitList (xs.map signedBits)).length

theorem program_executes (g : BitString → ℕ) (x : ℤ) (xs : List ℤ) :
    ∃ t, program.Executes g (store (signedBits x) (encodeBitList (xs.map signedBits)) [] [] [] [])
      (store (signedBits x) (encodeBitList (xs.map signedBits))
        (encodeBitList ((SpectralCoefficients.coefficients xs).map signedBits)) (signedBits (denominator x xs)) [] []) t ∧
      t≤time.eval (inputLength x xs) := by
  let roots := encodeBitList (xs.map signedBits)
  let nums := encodeBitList ((SpectralCoefficients.coefficients xs).map signedBits)
  let D := signedBits (denominator x xs)
  let N := inputLength x xs
  let s₀ := store (signedBits x) roots [] [] [] []
  let s₁ := store (signedBits x) roots [] [] roots []
  let s₂ := store (signedBits x) roots [] [] nums []
  let s₃ := store (signedBits x) roots nums [] [] []
  let s₄ := store (signedBits x) roots nums [] (signedBits x) []
  let s₅ := store (signedBits x) roots nums [] (signedBits x) roots
  let s₆ := store (signedBits x) roots nums [] D []
  let s₇ := store (signedBits x) roots nums D [] []
  have h₁ : (copyOn (1:Fin 27) 4 6 (by decide) (by decide) (by decide)).Executes g s₀ s₁ (5*roots.length+2) := by
    convert copyOn_executes g (1:Fin 27) 4 6 (by decide) (by decide) (by decide) s₀ rfl using 1
    funext i;fin_cases i <;> simp [s₀,s₁,store]
  obtain ⟨c,hc,hcb⟩ := SpectralCoefficients.programOn_executes coefficientEmbedding g s₁ xs
    (by funext i;fin_cases i <;> rfl)
  have h₂ : (SpectralCoefficients.programOn coefficientEmbedding).Executes g s₁ s₂ c := by
    convert hc using 1
    funext i;fin_cases i <;> simp [s₁,s₂,store,coefficientEmbedding,nums]
  have h₃ : (moveOn (4:Fin 27) 2 6 (by decide) (by decide) (by decide)).Executes g s₂ s₃ (6*nums.length+5) := by
    convert moveOn_executes g (4:Fin 27) 2 6 (by decide) (by decide) (by decide) s₂ rfl using 1
    funext i;fin_cases i <;> simp [s₂,s₃,store]
  have h₄ : (copyOn (0:Fin 27) 4 6 (by decide) (by decide) (by decide)).Executes g s₃ s₄ (5*(signedBits x).length+2) := by
    convert copyOn_executes g (0:Fin 27) 4 6 (by decide) (by decide) (by decide) s₃ rfl using 1
    funext i;fin_cases i <;> simp [s₃,s₄,store]
  have h₅ : (copyOn (1:Fin 27) 5 6 (by decide) (by decide) (by decide)).Executes g s₄ s₅ (5*roots.length+2) := by
    convert copyOn_executes g (1:Fin 27) 5 6 (by decide) (by decide) (by decide) s₄ rfl using 1
    funext i;fin_cases i <;> simp [s₄,s₅,store]
  obtain ⟨d,hd,hdb⟩ := SpectralDenominator.programOn_executes denominatorEmbedding g s₅ x xs
    (by funext i;fin_cases i <;> rfl)
  have h₆ : (SpectralDenominator.programOn denominatorEmbedding).Executes g s₅ s₆ d := by
    convert hd using 1
    funext i;fin_cases i <;> simp [s₅,s₆,store,denominatorEmbedding,D]
  have h₇ : (moveOn (4:Fin 27) 3 6 (by decide) (by decide) (by decide)).Executes g s₆ s₇ (6*D.length+5) := by
    convert moveOn_executes g (4:Fin 27) 3 6 (by decide) (by decide) (by decide) s₆ rfl using 1
    funext i;fin_cases i <;> simp [s₆,s₇,store]
  have hr : roots.length≤N := by unfold N inputLength roots;omega
  have hx : (signedBits x).length≤N := by unfold N inputLength;omega
  have hlen : xs.length≤N := by
    have hh := list_length_le_encodeBitList_length (xs.map signedBits)
    simp only [List.length_map] at hh
    exact hh.trans hr
  have hxs : ∀a∈xs,(signedBits a).length≤N := by
    intro a ha;exact (member_length_le_encodeBitList (List.mem_map.mpr ⟨a,ha,rfl⟩)).trans hr
  have hnums := SpectralCoefficients.coefficientStream_length xs N hlen hxs
  have hD := SpectralDenominator.denominator_length x xs N hx hxs hlen
  have hcM := polynomial_nat_eval_mono SpectralCoefficients.time hr
  dsimp only at hcM
  refine ⟨(5*roots.length+2)+(c+((6*nums.length+5)+((5*(signedBits x).length+2)+((5*roots.length+2)+(d+(6*D.length+5)+2)+2)+2)+2)+2)+2,
    seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃
      (seq_executes _ _ g h₄ (seq_executes _ _ g h₅ (seq_executes _ _ g h₆ h₇))))),?_⟩
  simp only [time,eval_add,eval_mul,eval_X,eval_ofNat,SpectralDenominator.registerBound,eval_one]
  change d≤SpectralDenominator.time.eval N at hdb
  change c≤SpectralCoefficients.time.eval roots.length at hcb
  change nums.length≤SpectralCoefficients.coefficientStreamBound.eval N at hnums
  change D.length≤(N+1)*N+2 at hD
  have hN : (signedBits x).length+roots.length=N := rfl
  change _≤SpectralCoefficients.time.eval N+SpectralDenominator.time.eval N+10*N+
    6*SpectralCoefficients.coefficientStreamBound.eval N+6*((N+1)*N+2)+28
  omega

theorem program_queryFree : program.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (SpectralCoefficients.programOn_queryFree _)
      (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _)
        (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
          (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
            (seq_queryFree _ _ (SpectralDenominator.programOn_queryFree _) (moveOn_queryFree _ _ _ _ _ _))))))

noncomputable def programOn {k : ℕ} (φ : Fin 27 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem programOn_executes {k : ℕ} (φ : Fin 27 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (x : ℤ) (xs : List ℤ) (hs : s∘φ=store (signedBits x) (encodeBitList (xs.map signedBits)) [] [] [] []) :
    ∃ t, (programOn φ).Executes g s
      (Function.update (Function.update s (φ 2) (encodeBitList ((SpectralCoefficients.coefficients xs).map signedBits)))
        (φ 3) (signedBits (denominator x xs))) t ∧ t≤time.eval (inputLength x xs) := by
  obtain ⟨t,ht,hb⟩ := program_executes g x xs
  refine ⟨t,?_,hb⟩
  apply rename_executes_to program φ g ht hs
  · have he : (Function.update (Function.update s (φ 2) (encodeBitList ((SpectralCoefficients.coefficients xs).map signedBits)))
        (φ 3) (signedBits (denominator x xs)))∘φ=
        Function.update (Function.update (s∘φ) 2 (encodeBitList ((SpectralCoefficients.coefficients xs).map signedBits)))
          3 (signedBits (denominator x xs)) := by
      funext i;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i;fin_cases i <;> rfl
  · intro j hj;rw [Function.update_of_ne (hj 3).symm,Function.update_of_ne (hj 2).symm]

theorem programOn_queryFree {k : ℕ} (φ : Fin 27 ↪ Fin (k+1)) : (programOn φ).QueryFree :=
  rename_queryFree _ _ program_queryFree
end HiddenCircuits.Circuit.Runtime.SpectralBasis
