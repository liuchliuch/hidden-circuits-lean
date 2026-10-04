import HiddenCircuits.Circuit.Runtime.RestoringEdgeEmitterLoops

/-! A complete restoring edge emitter: descending route, forbid, ascending
inverse route, with preserved endpoint data and clean work stacks. -/
namespace HiddenCircuits.Circuit.Runtime.RestoringEdgeEmitter
open HiddenCircuits.Complexity OracleBlock Polynomial

def bits (lo d : ℕ) : BitString :=
  descendingBits lo d ++ GateEmitter.chunk .forbid lo ++ ascendingBits (lo+1) d

noncomputable def program : OracleBlock 7 :=
  seq (copyOn 0 3 7 (by decide) (by decide) (by decide))
    (seq (copyOn 1 3 7 (by decide) (by decide) (by decide))
      (seq (copyOn 1 4 7 (by decide) (by decide) (by decide))
        (seq descend (seq forbid (seq (push 3 true)
          (seq (copyOn 1 4 7 (by decide) (by decide) (by decide)) (seq ascend (clear 3))))))))

noncomputable def timeBound : Polynomial ℕ := 3000*(X+1)^2

/-- Every route gate and paired-list delimiter is emitted by actual finite
instructions. Placement and distance masters survive unchanged. -/
theorem program_executes (g : BitString → ℕ) (lo d : ℕ) (out : BitString) :
    ∃ cost, program.Executes g (store lo d 0 0 out [] [] [])
      (store lo d 0 0 ((bits lo d).reverse++out) [] [] []) cost ∧ cost≤timeBound.eval (lo+d) := by
  have h1 : (copyOn (0:Fin 8) 3 7 (by decide) (by decide) (by decide)).Executes g
      (store lo d 0 0 out [] [] []) (store lo d lo 0 out [] [] []) (5*lo+2) := by
    convert copyOn_executes g (0:Fin 8) 3 7 (by decide) (by decide) (by decide) (store lo d 0 0 out [] [] []) rfl using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  have h2 : (copyOn (1:Fin 8) 3 7 (by decide) (by decide) (by decide)).Executes g
      (store lo d lo 0 out [] [] []) (store lo d (lo+d) 0 out [] [] []) (5*d+2) := by
    convert copyOn_executes g (1:Fin 8) 3 7 (by decide) (by decide) (by decide) (store lo d lo 0 out [] [] []) rfl using 1
    · funext i;fin_cases i <;> simp [store,←List.replicate_add,Nat.add_comm]
    · simp [store]
  have h3 : (copyOn (1:Fin 8) 4 7 (by decide) (by decide) (by decide)).Executes g
      (store lo d (lo+d) 0 out [] [] []) (store lo d (lo+d) d out [] [] []) (5*d+2) := by
    convert copyOn_executes g (1:Fin 8) 4 7 (by decide) (by decide) (by decide) (store lo d (lo+d) 0 out [] [] []) rfl using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  obtain ⟨cd,hd,hbd⟩ := descend_executes g lo d lo d out
  let a := (descendingBits lo d).reverse++out
  have h5 := forbid_executes g lo d lo 0 a
  let b := (GateEmitter.chunk .forbid lo).reverse++a
  have h6 : (push (3:Fin 8) true).Executes g (store lo d lo 0 b [] [] []) (store lo d (lo+1) 0 b [] [] []) 1 := by
    convert push_executes g (3:Fin 8) true (store lo d lo 0 b [] [] []) using 1
    funext i;fin_cases i <;> simp [store,List.replicate_succ]
  have h7 : (copyOn (1:Fin 8) 4 7 (by decide) (by decide) (by decide)).Executes g
      (store lo d (lo+1) 0 b [] [] []) (store lo d (lo+1) d b [] [] []) (5*d+2) := by
    convert copyOn_executes g (1:Fin 8) 4 7 (by decide) (by decide) (by decide) (store lo d (lo+1) 0 b [] [] []) rfl using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  obtain ⟨ca,ha,hba⟩ := ascend_executes g lo d (lo+1) d b
  let c := (ascendingBits (lo+1) d).reverse++b
  have h9 : (clear (3:Fin 8)).Executes g (store lo d (lo+1+d) 0 c [] [] [])
      (store lo d 0 0 c [] [] []) (lo+d+2) := by
    convert clear_executes g (3:Fin 8) (store lo d (lo+1+d) 0 c [] [] []) using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store];omega
  have h := seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 (seq_executes _ _ g hd
    (seq_executes _ _ g h5 (seq_executes _ _ g h6 (seq_executes _ _ g h7 (seq_executes _ _ g ha h9)))))))
  have he : c=(bits lo d).reverse++out := by simp [c,b,a,bits,List.reverse_append,List.append_assoc]
  rw [he] at h
  refine ⟨_,h,?_⟩
  let N := lo+d+1
  have hN : 1≤N := by dsimp [N];omega
  have hD : d≤N := by dsimp [N];omega
  have hdn := Nat.mul_le_mul_right N hD
  have hdm := Nat.mul_le_mul_left d (show 126*(lo+d)+716≤126*N+716 by dsimp [N];omega)
  have had : ca≤d*(126*N+716)+1 := by simpa [N,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hba
  have hdd : cd≤d*(126*N+716)+1 := hbd.trans (Nat.add_le_add_right hdm 1)
  have hlinear : 20*lo+16*d+97≤117*N := by dsimp [N];omega
  simp only [timeBound,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
  change _≤3000*N^2
  nlinarith

lemma program_queryFree : program.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ descend_queryFree
      (seq_queryFree _ _ forbid_queryFree (seq_queryFree _ _ (push_queryFree _ _)
        (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ ascend_queryFree (clear_queryFree _))))))))

noncomputable def on {k : ℕ} (φ : Fin 8 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 8 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k) (lo d : ℕ)
    (hs : s ∘ φ=store lo d 0 0 (s (φ 2)) [] [] []) :
    ∃ cost, (on φ).Executes g s (Function.update s (φ 2) ((bits lo d).reverse++s (φ 2))) cost ∧
      cost≤timeBound.eval (lo+d) := by
  obtain ⟨co,hc,hb⟩ := program_executes g lo d (s (φ 2))
  refine ⟨co,?_,hb⟩
  apply rename_executes_to _ φ g hc hs
  · have he : (Function.update s (φ 2) ((bits lo d).reverse++s (φ 2))) ∘ φ=
        Function.update (s ∘ φ) 2 ((bits lo d).reverse++s (φ 2)) := by
      funext i;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i;fin_cases i <;> rfl
  · intro i hi;exact Function.update_of_ne (hi 2).symm _ _
lemma on_queryFree {k : ℕ} (φ : Fin 8 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ program_queryFree

end HiddenCircuits.Circuit.Runtime.RestoringEdgeEmitter
