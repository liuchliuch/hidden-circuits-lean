import HiddenCircuits.Complexity.DeterminantRuntime.GatherLoop

/-! A fixed 14-stack indexed gather program, clean framed interface. -/
namespace HiddenCircuits.Complexity.DeterminantRuntime.Gather
open OracleBlock BinaryArithmetic

noncomputable def setup : OracleBlock 13 := seq
  (copyOn 1 5 9 (by decide) (by decide) (by decide))
  (copyOn 3 6 9 (by decide) (by decide) (by decide))

noncomputable def finish : OracleBlock 13 := seq (clear 5) (reverseOn 8 4 (by decide))
noncomputable def program : OracleBlock 13 := seq setup (seq loop finish)

theorem setup_executes (g : BitString → ℕ) (data : BitString) (start stride count : ℕ) (out : BitString) :
    setup.Executes g (store data start stride count out)
      (state data start stride count out start count [] []) (5*start+5*count+6) := by
  have h1 : (copyOn (1 : Fin 14) 5 9 (by decide) (by decide) (by decide)).Executes g
      (store data start stride count out) (state data start stride count out start 0 [] [])
      (5*start+2) := by
    have h := copyOn_executes g (1 : Fin 14) 5 9 (by decide) (by decide) (by decide)
      (store data start stride count out) rfl
    have he : Function.update (store data start stride count out) 5 (List.replicate start true) =
        state data start stride count out start 0 [] [] := by
      funext i; fin_cases i <;> rfl
    simpa only [show store data start stride count out 1 = List.replicate start true from rfl,
      show store data start stride count out 5 = [] from rfl,
      List.length_replicate, List.append_nil, he] using h
  have h2 : (copyOn (3 : Fin 14) 6 9 (by decide) (by decide) (by decide)).Executes g
      (state data start stride count out start 0 [] [])
      (state data start stride count out start count [] []) (5*count+2) := by
    have h := copyOn_executes g (3 : Fin 14) 6 9 (by decide) (by decide) (by decide)
      (state data start stride count out start 0 [] []) rfl
    have he : Function.update (state data start stride count out start 0 [] []) 6 (List.replicate count true) =
        state data start stride count out start count [] [] := by
      funext i; fin_cases i <;> rfl
    simpa only [show state data start stride count out start 0 [] [] 3 = List.replicate count true from rfl,
      show state data start stride count out start 0 [] [] 6 = [] from rfl,
      List.length_replicate, List.append_nil, he] using h
  convert seq_executes _ _ g h1 h2 using 1 <;> omega

theorem finish_executes (g : BitString → ℕ) (data : BitString) (start stride count : ℕ)
    (out : BitString) (position : ℕ) (acc : BitString) :
    finish.Executes g (state data start stride count out position 0 [] acc)
      (store data start stride count (acc.reverse++out)) (position+2*acc.length+4) := by
  have h1 : (clear (5 : Fin 14)).Executes g (state data start stride count out position 0 [] acc)
      (state data start stride count out 0 0 [] acc) (position+1) := by
    have h := clear_executes g (5 : Fin 14) (state data start stride count out position 0 [] acc)
    have he : Function.update (state data start stride count out position 0 [] acc) 5 [] =
        state data start stride count out 0 0 [] acc := by funext i; fin_cases i <;> rfl
    simpa only [show state data start stride count out position 0 [] acc 5 = List.replicate position true from rfl,
      List.length_replicate, he] using h
  have h2 : (reverseOn (8 : Fin 14) 4 (by decide)).Executes g
      (state data start stride count out 0 0 [] acc)
      (store data start stride count (acc.reverse++out)) (2*acc.length+1) := by
    convert reverseOn_executes g (8 : Fin 14) 4 (by decide)
      (state data start stride count out 0 0 [] acc) using 1
    funext i; fin_cases i <;> rfl
  convert seq_executes _ _ g h1 h2 using 1 <;> omega

def timeBound (L start stride count : ℕ) : ℕ :=
  5*start+5*count+
  count*(GraphReduction.Runtime.lookupBound L (start+stride*count)+6*L+5*stride+15)+
  start+stride*count+4*count*(L+1)+20

theorem executes (g : BitString → ℕ) (ws : List BitString) (start stride count : ℕ) (out : BitString) :
    ∃ t, program.Executes g (store (encodeBitList ws) start stride count out)
      (store (encodeBitList ws) start stride count (encodeBitList (words ws start stride count)++out)) t ∧
      t ≤ timeBound (encodeBitList ws).length start stride count := by
  obtain ⟨t,ht,hb⟩ := loop_execution g ws start stride count out start count (start+stride*count) [] (le_refl _)
  simp only [List.append_nil] at ht
  have hf := finish_executes g (encodeBitList ws) start stride count out (start+stride*count)
    (encodeBitList (words ws start stride count)).reverse
  simp only [List.reverse_reverse, List.length_reverse] at hf
  have h := seq_executes _ _ g (setup_executes g (encodeBitList ws) start stride count out)
    (seq_executes _ _ g (whilePop_executes _ _ _ g ht) hf)
  refine ⟨_,h,?_⟩
  have he := encoded_words_length ws start stride count
  unfold timeBound
  nlinarith

theorem queryFree : program.QueryFree := seq_queryFree _ _
  (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (copyOn_queryFree _ _ _ _ _ _))
  (seq_queryFree _ _ (whilePop_queryFree _ _ _ body_queryFree body_queryFree)
    (seq_queryFree _ _ (clear_queryFree _) (reverseOn_queryFree _ _ _)))

noncomputable def on {k : ℕ} (φ : Fin 14 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 14 ↪ Fin (k+1)) (g : BitString → ℕ)
    (ws : List BitString) (start stride count : ℕ) (out : BitString) (s : Store k)
    (hs : s ∘ φ = store (encodeBitList ws) start stride count out) :
    ∃ t, (on φ).Executes g s
      (Function.update s (φ 4) (encodeBitList (words ws start stride count)++out)) t ∧
      t ≤ timeBound (encodeBitList ws).length start stride count := by
  obtain ⟨t,ht,hb⟩ := executes g ws start stride count out
  refine ⟨t,?_,hb⟩
  apply rename_executes_to program φ g ht hs
  · have he : (Function.update s (φ 4) (encodeBitList (words ws start stride count)++out)) ∘ φ =
        Function.update (s ∘ φ) 4 (encodeBitList (words ws start stride count)++out) := by
      funext i; simp [Function.comp_def, Function.update_apply, φ.injective.eq_iff]
    rw [he,hs]
    funext i; fin_cases i <;> rfl
  · intro i hi
    exact Function.update_of_ne (hi 4).symm _ _

theorem on_queryFree {k : ℕ} (φ : Fin 14 ↪ Fin (k+1)) : (on φ).QueryFree :=
  rename_queryFree _ _ queryFree

end HiddenCircuits.Complexity.DeterminantRuntime.Gather
