import HiddenCircuits.Approximation.SamplerRuntime.LengthLess

/-! Read-only strict comparison of two word lengths, with copied clocks and charged cleanup. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.LengthLess
open Complexity
open OracleBlock

def readLessStore (a b out x y tmp : BitString) : Store 5 := fun i =>
  if i.val=0 then a else if i.val=1 then b else if i.val=2 then out
  else if i.val=3 then x else if i.val=4 then y else tmp

def readLessEmbedding : Fin 3 ↪ Fin 6 where
  toFun i := if i.val=0 then 3 else if i.val=1 then 4 else 2
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

noncomputable def readLessBlock : OracleBlock 5 :=
  seq (copyOn 0 3 5 (by decide) (by decide) (by decide))
    (seq (copyOn 1 4 5 (by decide) (by decide) (by decide))
      (seq (rename lengthLessBlock readLessEmbedding) (seq (clear 3) (clear 4))))

theorem readLess_executes (g : BitString → ℕ) (a b : BitString) :
    ∃ cost, readLessBlock.Executes g (readLessStore a b [] [] [] [])
      (readLessStore a b [decide (a.length<b.length)] [] [] []) cost ∧
      cost ≤ 13*(a.length+b.length)+23 := by
  have h₁ : (copyOn (0:Fin 6) 3 5 (by decide) (by decide) (by decide)).Executes g
      (readLessStore a b [] [] [] []) (readLessStore a b [] a [] []) (5*a.length+2) := by
    convert copyOn_executes g (0:Fin 6) 3 5 (by decide) (by decide) (by decide)
      (readLessStore a b [] [] [] []) rfl using 1
    funext i;fin_cases i <;> simp [readLessStore]
  have h₂ : (copyOn (1:Fin 6) 4 5 (by decide) (by decide) (by decide)).Executes g
      (readLessStore a b [] a [] []) (readLessStore a b [] a b []) (5*b.length+2) := by
    convert copyOn_executes g (1:Fin 6) 4 5 (by decide) (by decide) (by decide)
      (readLessStore a b [] a [] []) rfl using 1
    funext i;fin_cases i <;> simp [readLessStore]
  obtain ⟨x,y,c,hc,hcb⟩ := lengthLess_executes g a b []
  have hb := hc.stack_bound (n:=a.length+b.length) (by
    intro i
    fin_cases i
    · change a.length ≤ a.length+b.length; omega
    · change b.length ≤ a.length+b.length; omega
    · change 0 ≤ a.length+b.length; omega)
  have hx : x.length ≤ a.length+b.length+c := hb (0:Fin 3)
  have hy : y.length ≤ a.length+b.length+c := hb (1:Fin 3)
  have h₃ : (rename lengthLessBlock readLessEmbedding).Executes g
      (readLessStore a b [] a b []) (readLessStore a b [decide (a.length<b.length)] x y []) c := by
    apply rename_executes_to lengthLessBlock readLessEmbedding g hc
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro j hj
      fin_cases j
      all_goals first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) | exact False.elim (hj 2 rfl)
  have h₄ : (clear (3:Fin 6)).Executes g (readLessStore a b [decide (a.length<b.length)] x y [])
      (readLessStore a b [decide (a.length<b.length)] [] y []) (x.length+1) := by
    convert clear_executes g (3:Fin 6) (readLessStore a b [decide (a.length<b.length)] x y []) using 1
    funext i;fin_cases i <;> rfl
  have h₅ : (clear (4:Fin 6)).Executes g (readLessStore a b [decide (a.length<b.length)] [] y [])
      (readLessStore a b [decide (a.length<b.length)] [] [] []) (y.length+1) := by
    convert clear_executes g (4:Fin 6) (readLessStore a b [decide (a.length<b.length)] [] y []) using 1
    funext i;fin_cases i <;> rfl
  refine ⟨(5*a.length+2)+((5*b.length+2)+(c+((x.length+1)+(y.length+1)+2)+2)+2)+2,
    seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ (seq_executes _ _ g h₄ h₅))),?_⟩
  have hm : min a.length b.length ≤ a.length+b.length := by omega
  omega

 theorem readLess_queryFree : readLessBlock.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (rename_queryFree _ _ lengthLess_queryFree)
      (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _))))

noncomputable def readLessOn {k : ℕ} (φ : Fin 6 ↪ Fin (k+1)) : OracleBlock k := rename readLessBlock φ

/-- Outside the six declared ports, the routine preserves every frame cell. -/
theorem readLessOn_executes {k : ℕ} (φ : Fin 6 ↪ Fin (k+1)) (g : BitString → ℕ)
    (s : Store k) (a b : BitString) (hs : s∘φ=readLessStore a b [] [] [] []) :
    ∃ cost, (readLessOn φ).Executes g s (Function.update s (φ 2) [decide (a.length<b.length)]) cost ∧
      cost ≤ 13*(a.length+b.length)+23 := by
  obtain ⟨c,hc,hcb⟩ := readLess_executes g a b
  refine ⟨c,?_,hcb⟩
  apply rename_executes_to readLessBlock φ g hc hs
  · have he : (Function.update s (φ 2) [decide (a.length<b.length)])∘φ=
        Function.update (s∘φ) 2 [decide (a.length<b.length)] := by
      funext i;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i;fin_cases i <;> rfl
  · intro j hj
    exact Function.update_of_ne (hj 2).symm _ _

 theorem readLessOn_queryFree {k : ℕ} (φ : Fin 6 ↪ Fin (k+1)) : (readLessOn φ).QueryFree :=
  rename_queryFree _ _ readLess_queryFree

end HiddenCircuits.Approximation.SamplerRuntime.LengthLess
