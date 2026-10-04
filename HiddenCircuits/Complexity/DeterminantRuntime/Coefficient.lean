import HiddenCircuits.Complexity.DeterminantRuntime.CoefficientPrepare
import HiddenCircuits.Complexity.PolynomialBounds

/-! Charged exact signed division for the next Faddeev coefficient. -/
namespace HiddenCircuits.Complexity.DeterminantRuntime.Coefficient
open OracleBlock BinaryArithmetic Polynomial

noncomputable def divide : OracleBlock 12 := rename cleanDivide divisionPorts
noncomputable def program : OracleBlock 12 := seq denominatorProgram
  (seq (copyOn 1 2 3 (by decide) (by decide) (by decide)) (seq (Negation.negateOn 2) divide))

theorem divide_executes (g : BitString → ℕ) (k : ℕ) (trace : ℤ)
    (hdiv : ((k+1 : ℕ) : ℤ) ∣ -trace) :
    ∃ t, divide.Executes g
      (state k (signedBits trace) (signedBits (-trace)) [] (signedBits ((k+1 : ℕ) : ℤ)))
      (store k (signedBits trace) (signedBits ((-trace) / (k+1 : ℕ)))) t ∧
      t ≤ cleanDivideTime.eval ((signedBits trace).length+(signedBits ((k+1 : ℕ) : ℤ)).length) := by
  obtain ⟨t,ht,hb⟩ := cleanDivide_executes g (-trace) ((k+1 : ℕ) : ℤ) (by omega) hdiv
  refine ⟨t,?_,?_⟩
  · apply rename_executes_to cleanDivide divisionPorts g ht
    · funext q; fin_cases q <;> rfl
    · funext q; fin_cases q <;> rfl
    · intro q hq; fin_cases q <;> first | exact (hq 0 rfl).elim | exact (hq 1 rfl).elim | rfl
  · simpa only [signedBits,List.length_cons,Int.natAbs_neg] using hb

noncomputable def timePolynomial : Polynomial ℕ := cleanDivideTime.comp (2*X+3)+20*(X+1)^2+50

theorem executes (g : BitString → ℕ) (k : ℕ) (trace : ℤ)
    (hdiv : ((k+1 : ℕ) : ℤ) ∣ -trace) :
    ∃ t, program.Executes g (store k (signedBits trace) [])
      (store k (signedBits trace) (signedBits ((-trace) / (k+1 : ℕ)))) t ∧
      t ≤ timePolynomial.eval (k+(signedBits trace).length+1) := by
  obtain ⟨a,ha,hab⟩ := denominator_executes g k (signedBits trace)
  let den := signedBits ((k+1 : ℕ) : ℤ)
  let s := state k (signedBits trace) [] [] den
  let s1 := state k (signedBits trace) (signedBits trace) [] den
  let s2 := state k (signedBits trace) (signedBits (-trace)) [] den
  have hc : (copyOn (1 : Fin 13) 2 3 (by decide) (by decide) (by decide)).Executes g s s1
      (5*(signedBits trace).length+2) := by
    have h := copyOn_executes g (1 : Fin 13) 2 3 (by decide) (by decide) (by decide) s rfl
    have he : Function.update s 2 (signedBits trace) = s1 := by funext q; fin_cases q <;> rfl
    simpa only [show s 1 = signedBits trace from rfl, show s 2 = [] from rfl,List.append_nil,he] using h
  obtain ⟨b,hb,hbb⟩ := Negation.negateOn_executes g (2 : Fin 13) s1 trace rfl
  have he : Function.update s1 2 (signedBits (-trace)) = s2 := by funext q; fin_cases q <;> rfl
  rw [he] at hb
  obtain ⟨c,hcdiv,hcb⟩ := divide_executes g k trace hdiv
  have h := seq_executes _ _ g ha (seq_executes _ _ g hc (seq_executes _ _ g hb hcdiv))
  refine ⟨_,h,?_⟩
  have hden : (signedBits ((k+1 : ℕ) : ℤ)).length ≤ k+2 := by
    have hsz : (k+1).size ≤ k+1 := Nat.size_le.mpr Nat.lt_two_pow_self
    simpa only [signedBits,List.length_cons,encodeNat_length,Int.natAbs_natCast] using Nat.add_le_add_right hsz 1
  have hm := polynomial_nat_eval_mono cleanDivideTime
    (show (signedBits trace).length+(signedBits ((k+1 : ℕ) : ℤ)).length ≤
      2*(k+(signedBits trace).length+1)+3 by omega)
  simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_mul,
    Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_pow,Polynomial.eval_one]
  dsimp only at hm
  nlinarith

theorem queryFree : program.QueryFree := seq_queryFree _ _ denominatorProgram_queryFree
  (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (Negation.negateOn_queryFree _)
    (rename_queryFree _ _ cleanDivide_queryFree)))

noncomputable def on {k : ℕ} (φ : Fin 13 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {m : ℕ} (φ : Fin 13 ↪ Fin (m+1)) (g : BitString → ℕ)
    (k : ℕ) (trace : ℤ) (hdiv : ((k+1 : ℕ) : ℤ) ∣ -trace) (s : Store m)
    (hs : s ∘ φ = store k (signedBits trace) []) :
    ∃ t, (on φ).Executes g s (Function.update s (φ 2) (signedBits ((-trace)/(k+1 : ℕ)))) t ∧
      t ≤ timePolynomial.eval (k+(signedBits trace).length+1) := by
  obtain ⟨t,ht,hb⟩ := executes g k trace hdiv
  refine ⟨t,?_,hb⟩
  apply rename_executes_to program φ g ht hs
  · have he : (Function.update s (φ 2) (signedBits ((-trace)/(k+1 : ℕ)))) ∘ φ =
        Function.update (s ∘ φ) 2 (signedBits ((-trace)/(k+1 : ℕ))) := by
      funext q; simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext q; fin_cases q <;> rfl
  · intro q hq; exact Function.update_of_ne (hq 2).symm _ _

theorem on_queryFree {m : ℕ} (φ : Fin 13 ↪ Fin (m+1)) : (on φ).QueryFree := rename_queryFree _ _ queryFree

end HiddenCircuits.Complexity.DeterminantRuntime.Coefficient
