import HiddenCircuits.Complexity.BinaryArithmetic.WeightRuntime
import HiddenCircuits.Complexity.OracleMove
import HiddenCircuits.Complexity.PolynomialBounds

/-! Actual runtime generation of the three signed weights for a grid cell from
its four physical unary index/complement stacks. -/
namespace HiddenCircuits.Complexity.GridWeightsRuntime
open OracleBlock BinaryArithmetic Polynomial

/-- Two preserved unary masters, two output words, and twelve real work stacks. -/
def pairStore (i k : ℕ) (den num a b : BitString) : Store 15 := fun q =>
  if q.val=0 then List.replicate i true else if q.val=1 then List.replicate k true else
  if q.val=2 then den else if q.val=3 then num else if q.val=4 then a else if q.val=5 then b else []

def pairEmbedding : Fin 12 ↪ Fin 16 where
  toFun i := ⟨i.val+4,by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have hh := congrArg (fun q : Fin 16 => q.val) h
    change i.val+4=j.val+4 at hh
    omega
noncomputable def pairCompute : OracleBlock 15 := rename weightPairUnary pairEmbedding
noncomputable def pairProgram : OracleBlock 15 :=
  seq (copyOn 0 4 6 (by decide) (by decide) (by decide))
    (seq (copyOn 1 5 6 (by decide) (by decide) (by decide))
      (seq pairCompute (seq (moveOn 4 2 6 (by decide) (by decide) (by decide))
        (moveOn 5 3 6 (by decide) (by decide) (by decide)))))
noncomputable def pairTime : Polynomial ℕ := weightPairUnaryTime+5*X+12*(X^2+2)+22

theorem pairProgram_executes (g : BitString → ℕ) (d : ℕ) (i : Fin (d+1)) :
    ∃ c, pairProgram.Executes g (pairStore i.val (d-i.val) [] [] [] [])
      (pairStore i.val (d-i.val) (signedBits (interpolationDenominator d i))
        (signedBits (interpolationNegativeNumerator d i)) [] []) c ∧ c≤pairTime.eval d := by
  have h₀ : (copyOn (0 : Fin 16) 4 6 (by decide) (by decide) (by decide)).Executes g
      (pairStore i.val (d-i.val) [] [] [] [])
      (pairStore i.val (d-i.val) [] [] (List.replicate i.val true) []) (5*i.val+2) := by
    convert copyOn_executes g (0 : Fin 16) 4 6 (by decide) (by decide) (by decide)
      (pairStore i.val (d-i.val) [] [] [] []) rfl using 1
    · funext q;fin_cases q <;> simp [pairStore]
    · simp [pairStore]
  have h₁ : (copyOn (1 : Fin 16) 5 6 (by decide) (by decide) (by decide)).Executes g
      (pairStore i.val (d-i.val) [] [] (List.replicate i.val true) [])
      (pairStore i.val (d-i.val) [] [] (List.replicate i.val true) (List.replicate (d-i.val) true)) (5*(d-i.val)+2) := by
    convert copyOn_executes g (1 : Fin 16) 5 6 (by decide) (by decide) (by decide)
      (pairStore i.val (d-i.val) [] [] (List.replicate i.val true) []) rfl using 1
    · funext q;fin_cases q <;> simp [pairStore]
    · simp [pairStore]
  obtain ⟨c,hc,hb⟩ := weightPairUnary_executes g d i
  have h₂ : pairCompute.Executes g
      (pairStore i.val (d-i.val) [] [] (List.replicate i.val true) (List.replicate (d-i.val) true))
      (pairStore i.val (d-i.val) [] [] (signedBits (interpolationDenominator d i))
        (signedBits (interpolationNegativeNumerator d i))) c := by
    apply rename_executes_to weightPairUnary pairEmbedding g hc
    · funext q;fin_cases q <;> rfl
    · funext q;fin_cases q <;> rfl
    · intro q hq;fin_cases q <;> first | rfl | (exfalso;exact hq 0 rfl) | (exfalso;exact hq 1 rfl)
  have h₃ : (moveOn (4 : Fin 16) 2 6 (by decide) (by decide) (by decide)).Executes g
      (pairStore i.val (d-i.val) [] [] (signedBits (interpolationDenominator d i)) (signedBits (interpolationNegativeNumerator d i)))
      (pairStore i.val (d-i.val) (signedBits (interpolationDenominator d i)) [] [] (signedBits (interpolationNegativeNumerator d i)))
      (6*(signedBits (interpolationDenominator d i)).length+5) := by
    convert moveOn_executes g (4 : Fin 16) 2 6 (by decide) (by decide) (by decide)
      (pairStore i.val (d-i.val) [] [] (signedBits (interpolationDenominator d i)) (signedBits (interpolationNegativeNumerator d i))) rfl using 1
    funext q;fin_cases q <;> simp [pairStore]
  have h₄ : (moveOn (5 : Fin 16) 3 6 (by decide) (by decide) (by decide)).Executes g
      (pairStore i.val (d-i.val) (signedBits (interpolationDenominator d i)) [] [] (signedBits (interpolationNegativeNumerator d i)))
      (pairStore i.val (d-i.val) (signedBits (interpolationDenominator d i)) (signedBits (interpolationNegativeNumerator d i)) [] [])
      (6*(signedBits (interpolationNegativeNumerator d i)).length+5) := by
    convert moveOn_executes g (5 : Fin 16) 3 6 (by decide) (by decide) (by decide)
      (pairStore i.val (d-i.val) (signedBits (interpolationDenominator d i)) [] [] (signedBits (interpolationNegativeNumerator d i))) rfl using 1
    funext q;fin_cases q <;> simp [pairStore]
  refine ⟨_,seq_executes _ _ g h₀ (seq_executes _ _ g h₁
    (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ h₄))),?_⟩
  have hi := interpolation_weights_bit_bound d i
  have his : i.val+(d-i.val)=d := Nat.add_sub_of_le (by omega)
  simp only [pairTime,eval_add,eval_mul,eval_X,eval_pow,eval_ofNat,
    signedBits,List.length_cons,encodeNat_length]
  omega

lemma pairProgram_queryFree : pairProgram.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (rename_queryFree _ _ weightPairUnary_queryFree)
      (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _) (moveOn_queryFree _ _ _ _ _ _))))

/-- Four preserved unary indices, three signed outputs, one discarded numerator,
and twelve clean work stacks. -/
def gridStore (i k j l : ℕ) (di dj nu spare : BitString) : Store 19 := fun q =>
  if q.val=0 then List.replicate i true else if q.val=1 then List.replicate k true else
  if q.val=2 then List.replicate j true else if q.val=3 then List.replicate l true else
  if q.val=4 then di else if q.val=5 then dj else if q.val=6 then nu else if q.val=7 then spare else []

def leftEmbedding : Fin 16 ↪ Fin 20 where
  toFun q := if q=0 then 0 else if q=1 then 1 else if q=2 then 4 else if q=3 then 7 else ⟨q.val+4,by omega⟩
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

def rightEmbedding : Fin 16 ↪ Fin 20 where
  toFun q := if q=0 then 2 else if q=1 then 3 else if q=2 then 5 else if q=3 then 6 else ⟨q.val+4,by omega⟩
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

noncomputable def program : OracleBlock 19 :=
  seq (rename pairProgram leftEmbedding) (seq (clear 7) (rename pairProgram rightEmbedding))
noncomputable def time : Polynomial ℕ := 2*pairTime+X^2+7

theorem program_executes (g : BitString → ℕ) (dx dy : ℕ) (i : Fin (dx+1)) (j : Fin (dy+1)) :
    ∃ c, program.Executes g (gridStore i.val (dx-i.val) j.val (dy-j.val) [] [] [] [])
      (gridStore i.val (dx-i.val) j.val (dy-j.val) (signedBits (interpolationDenominator dx i))
        (signedBits (interpolationDenominator dy j)) (signedBits (interpolationNegativeNumerator dy j)) []) c ∧
      c≤time.eval (dx+dy) := by
  obtain ⟨cx,hx,hbx⟩ := pairProgram_executes g dx i
  have h₀ : (rename pairProgram leftEmbedding).Executes g
      (gridStore i.val (dx-i.val) j.val (dy-j.val) [] [] [] [])
      (gridStore i.val (dx-i.val) j.val (dy-j.val) (signedBits (interpolationDenominator dx i)) [] []
        (signedBits (interpolationNegativeNumerator dx i))) cx := by
    apply rename_executes_to pairProgram leftEmbedding g hx
    · funext q;fin_cases q <;> rfl
    · funext q;fin_cases q <;> rfl
    · intro q hq;fin_cases q <;> first | rfl | (exfalso;exact hq 2 rfl) | (exfalso;exact hq 3 rfl)
  have h₁ : (clear (7 : Fin 20)).Executes g
      (gridStore i.val (dx-i.val) j.val (dy-j.val) (signedBits (interpolationDenominator dx i)) [] []
        (signedBits (interpolationNegativeNumerator dx i)))
      (gridStore i.val (dx-i.val) j.val (dy-j.val) (signedBits (interpolationDenominator dx i)) [] [] [])
      ((signedBits (interpolationNegativeNumerator dx i)).length+1) := by
    convert clear_executes g (7 : Fin 20)
      (gridStore i.val (dx-i.val) j.val (dy-j.val) (signedBits (interpolationDenominator dx i)) [] []
        (signedBits (interpolationNegativeNumerator dx i))) using 1
    funext q;fin_cases q <;> rfl
  obtain ⟨cy,hy,hby⟩ := pairProgram_executes g dy j
  have h₂ : (rename pairProgram rightEmbedding).Executes g
      (gridStore i.val (dx-i.val) j.val (dy-j.val) (signedBits (interpolationDenominator dx i)) [] [] [])
      (gridStore i.val (dx-i.val) j.val (dy-j.val) (signedBits (interpolationDenominator dx i))
        (signedBits (interpolationDenominator dy j)) (signedBits (interpolationNegativeNumerator dy j)) []) cy := by
    apply rename_executes_to pairProgram rightEmbedding g hy
    · funext q;fin_cases q <;> rfl
    · funext q;fin_cases q <;> rfl
    · intro q hq;fin_cases q <;> first | rfl | (exfalso;exact hq 2 rfl) | (exfalso;exact hq 3 rfl)
  refine ⟨_,seq_executes _ _ g h₀ (seq_executes _ _ g h₁ h₂),?_⟩
  have hxmono := polynomial_nat_eval_mono pairTime (show dx≤dx+dy by omega)
  have hymono := polynomial_nat_eval_mono pairTime (show dy≤dx+dy by omega)
  dsimp only at hxmono hymono
  have hbits := (interpolation_weights_bit_bound dx i).2
  have hpow : dx^2≤(dx+dy)^2 := Nat.pow_le_pow_left (by omega) 2
  simp only [time,eval_add,eval_mul,eval_X,eval_pow,eval_ofNat,signedBits,List.length_cons,encodeNat_length]
  omega

lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (rename_queryFree _ _ pairProgram_queryFree)
  (seq_queryFree _ _ (clear_queryFree _) (rename_queryFree _ _ pairProgram_queryFree))

noncomputable def programOn {k : ℕ} (φ : Fin 20 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem programOn_executes {k : ℕ} (φ : Fin 20 ↪ Fin (k+1)) (g : BitString → ℕ)
    (s : Store k) (dx dy : ℕ) (i : Fin (dx+1)) (j : Fin (dy+1))
    (hs : s∘φ=gridStore i.val (dx-i.val) j.val (dy-j.val) [] [] [] []) :
    ∃ c, (programOn φ).Executes g s
      (Function.update (Function.update (Function.update s (φ 4) (signedBits (interpolationDenominator dx i)))
        (φ 5) (signedBits (interpolationDenominator dy j))) (φ 6) (signedBits (interpolationNegativeNumerator dy j))) c ∧
      c≤time.eval (dx+dy) := by
  obtain ⟨c,hc,hb⟩ := program_executes g dx dy i j
  refine ⟨c,?_,hb⟩
  apply rename_executes_to program φ g hc hs
  · funext q
    have hq := congrFun hs q
    change s (φ q)=_ at hq
    simp only [Function.comp_def,Function.update_apply,φ.injective.eq_iff,hq]
    fin_cases q <;> rfl
  · intro q hq
    simp only [Function.update_of_ne (hq 4).symm,Function.update_of_ne (hq 5).symm,Function.update_of_ne (hq 6).symm]

lemma programOn_queryFree {k : ℕ} (φ : Fin 20 ↪ Fin (k+1)) : (programOn φ).QueryFree :=
  rename_queryFree _ _ program_queryFree

end HiddenCircuits.Complexity.GridWeightsRuntime
