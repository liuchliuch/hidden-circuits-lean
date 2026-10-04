import HiddenCircuits.Complexity.GridDenominatorDegree
import HiddenCircuits.Complexity.BinaryArithmetic.CleanOperations
import HiddenCircuits.Complexity.OracleMove

/-! Actual shared two-grid denominator generation, with n,m masters preserved. -/
namespace HiddenCircuits.Complexity.GridDenominatorRuntime
open OracleBlock BinaryArithmetic Polynomial

/-- Masters n,m are at0,1; output2; all eighteen auxiliary positions are empty. -/
def store (n m : ℕ) (input left right out : BitString) : Store 21 := fun i =>
  if i.val=0 then List.replicate n true else if i.val=1 then List.replicate m true
  else if i.val=2 then out else if i.val=3 then input else if i.val=20 then left
  else if i.val=21 then right else []

def leftEmbedding : Fin 18 ↪ Fin 22 where
  toFun i := ⟨i.val+3,by omega⟩
  inj' := by intro i j h;apply Fin.ext;have hh := congrArg (fun z : Fin 22 => z.val) h;change i.val+3=j.val+3 at hh;omega
def rightEmbedding : Fin 18 ↪ Fin 22 where
  toFun i := if i.val=17 then 21 else ⟨i.val+3,by omega⟩
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

def multiplyEmbedding : Fin 6 ↪ Fin 22 where
  toFun i := if i.val=0 then 20 else if i.val=1 then 21 else ⟨i.val+1,by omega⟩
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

noncomputable def program : OracleBlock 21 :=
  seq (copyOn 0 3 5 (by decide) (by decide) (by decide))
    (seq (rename degreeProduct leftEmbedding)
      (seq (copyOn 1 3 5 (by decide) (by decide) (by decide))
        (seq (rename degreeProduct rightEmbedding)
          (seq (rename cleanMultiply multiplyEmbedding) (moveOn 20 2 3 (by decide) (by decide) (by decide))))))

noncomputable def valueBound : Polynomial ℕ := 2*((X^2+1)*(X+1)+2)
noncomputable def time : Polynomial ℕ :=
  2*degreeTime+cleanMultiplyTime.comp valueBound+20*(X+1)+6*valueBound+30

 theorem degreeValue_grid (n m : ℕ) : degreeValue n*degreeValue m=gridDenominator n m := rfl

 theorem valueBound_pair (n m : ℕ) :
    (signedBits (degreeValue n)).length+(signedBits (degreeValue m)).length≤valueBound.eval (n+m) := by
  have hn := degreeValue_length n
  have hm := degreeValue_length m
  have h₁ : (n^2+1)*(n+1)+2≤((n+m)^2+1)*(n+m+1)+2 := by gcongr <;> omega
  have h₂ : (m^2+1)*(m+1)+2≤((n+m)^2+1)*(n+m+1)+2 := by gcongr <;> omega
  simp only [valueBound,eval_mul,eval_add,eval_pow,eval_X,eval_ofNat,eval_one]
  omega
 theorem valueBound_grid (n m : ℕ) : (signedBits (gridDenominator n m)).length≤valueBound.eval (n+m) := by
  have h := signedBits_length_of_abs_bound (gridDenominator_envelope n m)
  have h₁ : (n^2+1)*(n+1)≤((n+m)^2+1)*(n+m+1) := by gcongr <;> omega
  have h₂ : (m^2+1)*(m+1)≤((n+m)^2+1)*(n+m+1) := by gcongr <;> omega
  simp only [valueBound,eval_mul,eval_add,eval_pow,eval_X,eval_ofNat,eval_one]
  unfold denominatorExponent at h
  omega

/-- The output is the literal common integer denominator. Every weight and
product is computed by the finite instruction program, including signs. -/
theorem program_executes (g : BitString → ℕ) (n m : ℕ) :
    ∃ c, program.Executes g (store n m [] [] [] [])
      (store n m [] [] [] (signedBits (gridDenominator n m))) c ∧ c≤time.eval (n+m) := by
  let dn := signedBits (degreeValue n)
  let dm := signedBits (degreeValue m)
  let D := signedBits (gridDenominator n m)
  let s₀ := store n m [] [] [] []
  let s₁ := store n m (List.replicate n true) [] [] []
  let s₂ := store n m [] dn [] []
  let s₃ := store n m (List.replicate m true) dn [] []
  let s₄ := store n m [] dn dm []
  let s₅ := store n m [] D [] []
  let s₆ := store n m [] [] [] D
  have h₁ : (copyOn (0:Fin 22) 3 5 (by decide) (by decide) (by decide)).Executes g s₀ s₁ (5*n+2) := by
    convert copyOn_executes g (0:Fin 22) 3 5 (by decide) (by decide) (by decide) s₀ rfl using 1
    · funext i;fin_cases i <;> simp [s₀,s₁,store]
    · simp [s₀,store]
  obtain ⟨a,ha,hab⟩ := degree_executes g n
  have h₂ : (rename degreeProduct leftEmbedding).Executes g s₁ s₂ a := by
    apply rename_executes_to degreeProduct leftEmbedding g ha
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro j hj
      fin_cases j
      all_goals first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 17 rfl)
  have h₃ : (copyOn (1:Fin 22) 3 5 (by decide) (by decide) (by decide)).Executes g s₂ s₃ (5*m+2) := by
    convert copyOn_executes g (1:Fin 22) 3 5 (by decide) (by decide) (by decide) s₂ rfl using 1
    · funext i;fin_cases i <;> simp [s₂,s₃,store]
    · simp [s₂,store]
  obtain ⟨b,hb,hbb⟩ := degree_executes g m
  have h₄ : (rename degreeProduct rightEmbedding).Executes g s₃ s₄ b := by
    apply rename_executes_to degreeProduct rightEmbedding g hb
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro j hj
      fin_cases j
      all_goals first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 17 rfl)
  obtain ⟨c,hc,hcb⟩ := cleanMultiply_executes g (degreeValue n) (degreeValue m)
  rw [degreeValue_grid] at hc
  have h₅ : (rename cleanMultiply multiplyEmbedding).Executes g s₄ s₅ c := by
    apply rename_executes_to cleanMultiply multiplyEmbedding g hc
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro j hj
      fin_cases j
      all_goals first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl)
  have h₆ : (moveOn (20:Fin 22) 2 3 (by decide) (by decide) (by decide)).Executes g s₅ s₆ (6*D.length+5) := by
    convert moveOn_executes g (20:Fin 22) 2 3 (by decide) (by decide) (by decide) s₅ rfl using 1
    funext i;fin_cases i <;> simp [s₅,s₆,store]
  refine ⟨(5*n+2)+(a+((5*m+2)+(b+(c+(6*D.length+5)+2)+2)+2)+2)+2,
    seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃
      (seq_executes _ _ g h₄ (seq_executes _ _ g h₅ h₆)))),?_⟩
  have han := polynomial_nat_eval_mono degreeTime (show n≤n+m by omega)
  have hbm := polynomial_nat_eval_mono degreeTime (show m≤n+m by omega)
  have hcM := polynomial_nat_eval_mono cleanMultiplyTime (valueBound_pair n m)
  dsimp only at han hbm hcM
  have hD := valueBound_grid n m
  simp only [time,eval_add,eval_mul,eval_comp,eval_X,eval_ofNat,eval_one]
  dsimp [D]
  omega

 theorem program_queryFree : program.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (rename_queryFree _ _ degree_queryFree)
      (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
        (seq_queryFree _ _ (rename_queryFree _ _ degree_queryFree)
          (seq_queryFree _ _ (rename_queryFree _ _ cleanMultiply_queryFree) (moveOn_queryFree _ _ _ _ _ _)))))

noncomputable def programOn {k : ℕ} (φ : Fin 22 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem programOn_executes {k : ℕ} (φ : Fin 22 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (n m : ℕ) (hs : s∘φ=store n m [] [] [] []) :
    ∃ c, (programOn φ).Executes g s (Function.update s (φ 2) (signedBits (gridDenominator n m))) c ∧
      c≤time.eval (n+m) := by
  obtain ⟨c,hc,hcb⟩ := program_executes g n m
  refine ⟨c,?_,hcb⟩
  apply rename_executes_to program φ g hc hs
  · have he : (Function.update s (φ 2) (signedBits (gridDenominator n m)))∘φ=
        Function.update (s∘φ) 2 (signedBits (gridDenominator n m)) := by
      funext i;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i;fin_cases i <;> rfl
  · intro j hj;exact Function.update_of_ne (hj 2).symm _ _

theorem programOn_queryFree {k : ℕ} (φ : Fin 22 ↪ Fin (k+1)) : (programOn φ).QueryFree :=
  rename_queryFree _ _ program_queryFree
end HiddenCircuits.Complexity.GridDenominatorRuntime
