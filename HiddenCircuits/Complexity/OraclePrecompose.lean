import HiddenCircuits.Complexity.OracleCleanup
import HiddenCircuits.Complexity.PolynomialBounds

/-! Actual finite-program preprocessing and cleanup. This is a proved code
construction, rather than a postulated closure property for time complexity. -/
namespace HiddenCircuits.Complexity.OracleBlock
open Polynomial
variable {k l : ℕ}

def resizeEmbedding (h : k≤l) : Fin (k+1) ↪ Fin (l+1) where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun q : Fin (l+1) => q.val) h)

@[simp] lemma resizeEmbedding_zero (h : k≤l) : resizeEmbedding h 0=0 := rfl
noncomputable def resize (B : OracleBlock k) (h : k≤l) : OracleBlock l := rename B (resizeEmbedding h)

theorem resize_executes (B : OracleBlock k) (hkl : k≤l) (g : BitString → ℕ) (x : BitString)
    (s : Store k) (c : ℕ) (hc : B.Executes g (Function.update (fun _ => []) 0 x) s c) :
    ∃ t : Store l, (resize B hkl).Executes g (Function.update (fun _ => []) 0 x) t c ∧ t 0=s 0 := by
  let outer : Store l := Function.update (fun _ => []) 0 x
  have hi : outer ∘ resizeEmbedding hkl = Function.update (fun _ : Fin (k+1) => []) 0 x := by
    funext i
    by_cases h : i=0
    · subst i;simp [outer]
    · have hn : resizeEmbedding hkl i≠0 := by
        intro hh;apply h;apply (resizeEmbedding hkl).injective;simpa using hh
      simp [outer,Function.comp_def,h,hn]
  have hh := rename_executes B (resizeEmbedding hkl) g outer (by rw [hi];exact hc)
  refine ⟨_,hh,?_⟩
  simpa only [resizeEmbedding_zero] using install_image (resizeEmbedding hkl) outer s 0

noncomputable def precompose (B C : OracleBlock k) : OracleBlock k := seq B (seq (cleanup 0) C)
noncomputable def precomposeTime (p q size : Polynomial ℕ) : Polynomial ℕ :=
  p + Polynomial.C (k+1)*(X+p+3)+q.comp size+5

/-- Run an actual emitter, physically clear its work tapes, and then run an
actual downstream solver on the emitted string. The downstream bound is
substituted into the proved emitted-size polynomial. -/
theorem precompose_executes (B C : OracleBlock k) (g : BitString → ℕ)
    (emit result : BitString → BitString) (p q size : Polynomial ℕ)
    (hB : ∀ x, ∃ s : Store k, ∃ c, B.Executes g (Function.update (fun _ => []) 0 x) s c ∧
      s 0=emit x ∧ c≤p.eval x.length)
    (hsize : ∀ x, (emit x).length≤size.eval x.length)
    (hC : ∀ x, ∃ s : Store k, ∃ c, C.Executes g (Function.update (fun _ => []) 0 (emit x)) s c ∧
      s 0=result x ∧ c≤q.eval (emit x).length) (x : BitString) :
    ∃ s : Store k, ∃ c, (precompose B C).Executes g (Function.update (fun _ => []) 0 x) s c ∧
      s 0=result x ∧ c≤(precomposeTime (k := k) p q size).eval x.length := by
  obtain ⟨s,b,hb,ho,hbt⟩ := hB x
  obtain ⟨c,hc,hct⟩ := cleanup_executes g (0 : Fin (k+1)) s (x.length+b)
    (hb.stack_bound (B.machine.init_stack_bound x))
  rw [ho] at hc
  obtain ⟨t,d,hd,hto,hdt⟩ := hC x
  refine ⟨t,b+(c+d+2)+2,seq_executes _ _ g hb (seq_executes _ _ g hc hd),hto,?_⟩
  have hm := polynomial_nat_eval_mono q (hsize x)
  dsimp only at hm
  simp only [precomposeTime,eval_add,eval_mul,eval_C,eval_X,eval_ofNat,eval_comp]
  nlinarith

end HiddenCircuits.Complexity.OracleBlock
