import HiddenCircuits.Complexity.CNFCloneEmitter.VertexRuntime
import HiddenCircuits.Complexity.OracleRepeat

namespace HiddenCircuits.Complexity.CNFCloneEmitter.VertexRuntime
open OracleBlock

def tag : Descriptor → Bool
  | .variable _ _ => true
  | .clause _ => false
def number : Descriptor → ℕ
  | .variable i _ => i
  | .clause j => j
def sign : Descriptor → Bool
  | .variable _ b => b
  | .clause _ => false

theorem split_executes (g : BitString → ℕ) (x cut a b : ℕ) :
    ∃ cost, split.Executes g (store x cut a b [] 0 [] x cut 0 [] [] 0)
      (store x cut a b [decide (x<cut)] 0 [] (x-cut) 0 0 [] [] 0) cost ∧ cost≤9*cut+4 := by
  obtain ⟨c,hc,hb⟩ := UnarySplit.program_executes g x cut
  refine ⟨c,?_,hb⟩
  apply rename_executes_to _ splitEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | exact (hi 2 rfl).elim

lemma pop_tag (x cut a b y : ℕ) (flag : Bool) :
    Function.update (store x cut a b [flag] 0 [] y 0 0 [] [] 0) 4 []=store x cut a b [] 0 [] y 0 0 [] [] 0 := by
  funext i;fin_cases i <;> rfl

theorem classify_executes (g : BitString → ℕ) (x cut a b : ℕ)
    (ha : x<cut → 0<a) (hb : cut≤x → 0<b) :
    ∃ cost, classify.Executes g (store x cut a b [decide (x<cut)] 0 [] (x-cut) 0 0 [] [] 0)
      (store x cut a b [tag (decodeVertex cut a b x)] (number (decodeVertex cut a b x))
        [sign (decodeVertex cut a b x)] 0 0 0 [] [] 0) cost ∧ cost≤100*(x+cut+a+b+1)^2+2 := by
  by_cases hx : x<cut
  · obtain ⟨c,hc,hcB⟩ := variableBranch_executes g x cut a b (ha hx)
    have hbody : variableBranch.Executes g
        (Function.update (store x cut a b [true] 0 [] (x-cut) 0 0 [] [] 0) 4 [])
        (store x cut a b [true] ((x/a)/2) [decide ((x/a)%2=1)] 0 0 0 [] [] 0) c := by
      rw [pop_tag,Nat.sub_eq_zero_of_le hx.le];exact hc
    have h := branchPop_true 4 skip clauseBranch variableBranch g rfl hbody
    refine ⟨c+2,?_,?_⟩
    · simpa only [hx,decide_true,decodeVertex,if_pos,tag,number,sign] using h
    · have hm := Nat.pow_le_pow_left (show x+a+1≤x+cut+a+b+1 by omega) 2
      nlinarith
  · obtain ⟨c,hc,hcB⟩ := clauseBranch_executes g x cut a b (x-cut) (hb (by omega))
    have hbody : clauseBranch.Executes g
        (Function.update (store x cut a b [false] 0 [] (x-cut) 0 0 [] [] 0) 4 [])
        (store x cut a b [false] ((x-cut)/b) [false] 0 0 0 [] [] 0) c := by rw [pop_tag];exact hc
    have h := branchPop_false 4 skip clauseBranch variableBranch g rfl hbody
    refine ⟨c+2,?_,?_⟩
    · simpa only [hx,decide_false,decodeVertex,if_neg,tag,number,sign] using h
    · have hm := Nat.pow_le_pow_left (show x-cut+b+1≤x+cut+a+b+1 by omega) 2
      nlinarith

/-- Uniform vertex decoder with only branch-local divisor positivity. In
particular zero cloning activities are never excluded globally. -/
theorem program_executes (g : BitString → ℕ) (x cut a b : ℕ)
    (ha : x<cut → 0<a) (hb : cut≤x → 0<b) :
    ∃ cost, program.Executes g (store x cut a b [] 0 [] 0 0 0 [] [] 0)
      (store x cut a b [tag (decodeVertex cut a b x)] (number (decodeVertex cut a b x))
        [sign (decodeVertex cut a b x)] 0 0 0 [] [] 0) cost ∧ cost≤200*(x+cut+a+b+1)^2 := by
  have h1 : (copyOn (0:Fin 13) 7 11 (by decide) (by decide) (by decide)).Executes g
      (store x cut a b [] 0 [] 0 0 0 [] [] 0) (store x cut a b [] 0 [] x 0 0 [] [] 0) (5*x+2) := by
    convert copyOn_executes g (0:Fin 13) 7 11 (by decide) (by decide) (by decide)
      (store x cut a b [] 0 [] 0 0 0 [] [] 0) rfl using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  have h2 : (copyOn (1:Fin 13) 8 11 (by decide) (by decide) (by decide)).Executes g
      (store x cut a b [] 0 [] x 0 0 [] [] 0) (store x cut a b [] 0 [] x cut 0 [] [] 0) (5*cut+2) := by
    convert copyOn_executes g (1:Fin 13) 8 11 (by decide) (by decide) (by decide)
      (store x cut a b [] 0 [] x 0 0 [] [] 0) rfl using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  obtain ⟨cs,hs,hsB⟩ := split_executes g x cut a b
  obtain ⟨cc,hc,hcB⟩ := classify_executes g x cut a b ha hb
  refine ⟨5*x+2+((5*cut+2)+(cs+cc+2)+2)+2,
    seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g hs hc)),?_⟩
  let N := x+cut+a+b+1
  have hN : 1≤N := by dsimp [N];omega
  have hlin : 5*x+14*cut+16≤20*N := by dsimp [N];omega
  change cc≤100*N^2+2 at hcB
  change _ ≤200*N^2
  nlinarith

lemma variableBranch_queryFree : variableBranch.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (rename_queryFree _ _ UnaryDivision.block_queryFree)
      (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (prepend_queryFree _ _)
        (seq_queryFree _ _ (rename_queryFree _ _ UnaryDivision.block_queryFree)
          (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _
            (branchPop_queryFree _ _ _ _ (push_queryFree _ _) (push_queryFree _ _) (push_queryFree _ _))
            (push_queryFree _ _)))))))
lemma clauseBranch_queryFree : clauseBranch.QueryFree :=
  seq_queryFree _ _ (rename_queryFree _ _ UnaryDivision.block_queryFree)
    (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (push_queryFree _ _) (push_queryFree _ _)))
lemma program_queryFree : program.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (rename_queryFree _ _ UnarySplit.program_queryFree)
      (branchPop_queryFree _ _ _ _ skip_queryFree clauseBranch_queryFree variableBranch_queryFree)))

noncomputable def on {k : ℕ} (φ : Fin 13 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 13 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (x cut a b : ℕ) (ha : x<cut → 0<a) (hb : cut≤x → 0<b)
    (hs : s ∘ φ=store x cut a b [] 0 [] 0 0 0 [] [] 0) :
    ∃ cost, (on φ).Executes g s
      (Function.update (Function.update (Function.update s (φ 4) [tag (decodeVertex cut a b x)])
        (φ 5) (List.replicate (number (decodeVertex cut a b x)) true))
        (φ 6) [sign (decodeVertex cut a b x)]) cost ∧ cost≤200*(x+cut+a+b+1)^2 := by
  obtain ⟨c,hc,hB⟩ := program_executes g x cut a b ha hb
  refine ⟨c,?_,hB⟩
  apply rename_executes_to _ φ g hc hs
  · have he : (Function.update (Function.update (Function.update s (φ 4) [tag (decodeVertex cut a b x)])
        (φ 5) (List.replicate (number (decodeVertex cut a b x)) true))
        (φ 6) [sign (decodeVertex cut a b x)]) ∘ φ =
        Function.update (Function.update (Function.update (s ∘ φ) 4 [tag (decodeVertex cut a b x)])
          5 (List.replicate (number (decodeVertex cut a b x)) true)) 6 [sign (decodeVertex cut a b x)] := by
      funext i;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i;fin_cases i <;> rfl
  · intro i hi
    simp only [Function.update_of_ne (hi 4).symm,Function.update_of_ne (hi 5).symm,Function.update_of_ne (hi 6).symm]
lemma on_queryFree {k : ℕ} (φ : Fin 13 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ program_queryFree

end HiddenCircuits.Complexity.CNFCloneEmitter.VertexRuntime
