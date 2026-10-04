import HiddenCircuits.Complexity.CNFCloneEmitter.UnarySplit
import HiddenCircuits.Complexity.OracleMove
import HiddenCircuits.Complexity.OracleDropFixed

/-! Actual unary endpoint ordering and route distance for the restoring source
circuit. Source vertex indices are preserved byte-for-byte. -/
namespace HiddenCircuits.Circuit.Runtime.EdgeEndpoints
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

def store (u v lo d work sub : ℕ) (flag : BitString) : Store 7 := fun i =>
  if i.val=0 then List.replicate u true else if i.val=1 then List.replicate v true else
  if i.val=2 then List.replicate lo true else if i.val=3 then List.replicate d true else
  if i.val=4 then List.replicate work true else if i.val=5 then List.replicate sub true else if i.val=6 then flag else []

def splitEmbedding : Fin 3 ↪ Fin 8 where
  toFun i := if i.val=0 then 4 else if i.val=1 then 5 else 6
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
noncomputable def split : OracleBlock 7 := rename CNFCloneEmitter.UnarySplit.program splitEmbedding

def drop : OracleBlock 7 where
  labelCount:=2
  start:=0
  exit:=1
  code q := if q=0 then .pop 4 1 1 1 else .halt
  exit_halt:=rfl

noncomputable def finish (source : Fin 2) : OracleBlock 7 :=
  seq (copyOn (source.castLE (by decide)) 2 7 (by fin_cases source <;> decide)
      (by fin_cases source <;> decide) (by decide))
    (seq drop (moveOn 4 3 7 (by decide) (by decide) (by decide)))

lemma split_executes (g : BitString → ℕ) (u v x y : ℕ) :
    ∃ c, split.Executes g (store u v 0 0 x y [])
      (store u v 0 0 (x-y) 0 [decide (x<y)]) c ∧ c≤9*y+4 := by
  obtain ⟨c,hc,hb⟩ := CNFCloneEmitter.UnarySplit.program_executes g x y
  refine ⟨c,?_,hb⟩
  apply rename_executes_to _ splitEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | (exfalso;exact hi 0 rfl) | (exfalso;exact hi 1 rfl) | (exfalso;exact hi 2 rfl)

lemma drop_executes (g : BitString → ℕ) (u v lo x : ℕ) :
    drop.Executes g (store u v lo 0 x 0 []) (store u v lo 0 (x-1) 0 []) 1 := by
  apply OracleMachine.Steps.single
  cases x with
  | zero => rfl
  | succ x =>
    change some (drop.config drop.exit (Function.update (store u v lo 0 (x+1) 0 []) 4 (List.replicate x true)),1)=
      some (drop.config drop.exit (store u v lo 0 x 0 []),1)
    apply congrArg (fun s : Store 7 => some (drop.config drop.exit s,1))
    funext i;fin_cases i <;> rfl

lemma finish_executes (g : BitString → ℕ) (source : Fin 2) (u v x : ℕ) :
    (finish source).Executes g (store u v 0 0 x 0 [])
      (store u v (if source=0 then u else v) (x-1) 0 0 [])
      (5*(if source=0 then u else v)+6*(x-1)+12) := by
  let lo := if source=0 then u else v
  have h₀ : (copyOn (source.castLE (by decide)) (2 : Fin 8) 7 (by fin_cases source <;> decide)
      (by fin_cases source <;> decide) (by decide)).Executes g (store u v 0 0 x 0 [])
      (store u v lo 0 x 0 []) (5*lo+2) := by
    convert copyOn_executes g (source.castLE (by decide)) (2 : Fin 8) 7
      (by fin_cases source <;> decide) (by fin_cases source <;> decide) (by decide)
      (store u v 0 0 x 0 []) rfl using 1
    · funext i;fin_cases source <;> fin_cases i <;> simp [store,lo]
    · fin_cases source <;> simp [store,lo]
  have h₁ := drop_executes g u v lo x
  have h₂ : (moveOn (4 : Fin 8) 3 7 (by decide) (by decide) (by decide)).Executes g
      (store u v lo 0 (x-1) 0 []) (store u v lo (x-1) 0 0 []) (6*(x-1)+5) := by
    convert moveOn_executes g (4 : Fin 8) 3 7 (by decide) (by decide) (by decide)
      (store u v lo 0 (x-1) 0 []) rfl using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  convert seq_executes _ _ g h₀ (seq_executes _ _ g h₁ h₂) using 1 <;> omega

noncomputable def reverseBranch : OracleBlock 7 :=
  seq (copyOn 1 4 7 (by decide) (by decide) (by decide))
    (seq (copyOn 0 5 7 (by decide) (by decide) (by decide))
      (seq split (seq (clear 6) (finish 0))))

lemma reverseBranch_executes (g : BitString → ℕ) (u v : ℕ) (huv : u<v) :
    ∃ c, reverseBranch.Executes g (store u v 0 0 0 0 [])
      (store u v u (v-u-1) 0 0 []) c ∧ c≤19*u+11*v+30 := by
  have h₀ : (copyOn (1 : Fin 8) 4 7 (by decide) (by decide) (by decide)).Executes g
      (store u v 0 0 0 0 []) (store u v 0 0 v 0 []) (5*v+2) := by
    convert copyOn_executes g (1 : Fin 8) 4 7 (by decide) (by decide) (by decide) (store u v 0 0 0 0 []) rfl using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  have h₁ : (copyOn (0 : Fin 8) 5 7 (by decide) (by decide) (by decide)).Executes g
      (store u v 0 0 v 0 []) (store u v 0 0 v u []) (5*u+2) := by
    convert copyOn_executes g (0 : Fin 8) 5 7 (by decide) (by decide) (by decide) (store u v 0 0 v 0 []) rfl using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  obtain ⟨s,hs,hsb⟩ := split_executes g u v v u
  have h₂ : (clear (6 : Fin 8)).Executes g (store u v 0 0 (v-u) 0 [decide (v<u)])
      (store u v 0 0 (v-u) 0 []) 2 := by
    convert clear_executes g (6 : Fin 8) (store u v 0 0 (v-u) 0 [decide (v<u)]) using 1
    funext i;fin_cases i <;> rfl
  have hf : (finish 0).Executes g (store u v 0 0 (v-u) 0 [])
      (store u v u (v-u-1) 0 0 []) (5*u+6*(v-u-1)+12) := finish_executes g 0 u v (v-u)
  refine ⟨_,seq_executes _ _ g h₀ (seq_executes _ _ g h₁ (seq_executes _ _ g hs (seq_executes _ _ g h₂ hf))),?_⟩
  omega

noncomputable def choose : OracleBlock 7 := branchPop 6 skip (finish 1) reverseBranch
noncomputable def program : OracleBlock 7 :=
  seq (copyOn 0 4 7 (by decide) (by decide) (by decide))
    (seq (copyOn 1 5 7 (by decide) (by decide) (by decide)) (seq split choose))

lemma choose_executes (g : BitString → ℕ) (u v : ℕ) :
    ∃ c, choose.Executes g (store u v 0 0 (u-v) 0 [decide (u<v)])
      (store u v (min u v) (max u v-min u v-1) 0 0 []) c ∧ c≤20*u+20*v+34 := by
  by_cases h : u<v
  · have hu : u-v=0 := Nat.sub_eq_zero_of_le h.le
    obtain ⟨c,hc,hb⟩ := reverseBranch_executes g u v h
    have he : Function.update (store u v 0 0 (u-v) 0 [true]) (6 : Fin 8) []=store u v 0 0 0 0 [] := by
      funext i;fin_cases i <;> simp [store,hu]
    have hh := branchPop_true (6 : Fin 8) skip (finish 1) reverseBranch g
      (s := store u v 0 0 (u-v) 0 [true]) (rest := []) rfl (by rw [he];exact hc)
    exact ⟨c+2,by simpa [choose,h,Nat.min_eq_left h.le,Nat.max_eq_right h.le] using hh,by omega⟩
  · have hv : v≤u := by omega
    have he : Function.update (store u v 0 0 (u-v) 0 [false]) (6 : Fin 8) []=store u v 0 0 (u-v) 0 [] := by
      funext i;fin_cases i <;> rfl
    have hf := finish_executes g (1 : Fin 2) u v (u-v)
    have hh := branchPop_false (6 : Fin 8) skip (finish 1) reverseBranch g
      (s := store u v 0 0 (u-v) 0 [false]) (rest := []) rfl (by rw [he];exact hf)
    refine ⟨5*v+6*(u-v-1)+14,?_,?_⟩
    · simpa [choose,h,Nat.min_eq_right hv,Nat.max_eq_left hv] using hh
    · omega

/-- All comparisons, truncating subtraction, movement and clearing are actual
bit-stack executions. Equal endpoints safely produce distance zero as well. -/
theorem program_executes (g : BitString → ℕ) (u v : ℕ) :
    ∃ c, program.Executes g (store u v 0 0 0 0 [])
      (store u v (min u v) (max u v-min u v-1) 0 0 []) c ∧ c≤50*(u+v+1) := by
  have h₀ : (copyOn (0 : Fin 8) 4 7 (by decide) (by decide) (by decide)).Executes g
      (store u v 0 0 0 0 []) (store u v 0 0 u 0 []) (5*u+2) := by
    convert copyOn_executes g (0 : Fin 8) 4 7 (by decide) (by decide) (by decide) (store u v 0 0 0 0 []) rfl using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  have h₁ : (copyOn (1 : Fin 8) 5 7 (by decide) (by decide) (by decide)).Executes g
      (store u v 0 0 u 0 []) (store u v 0 0 u v []) (5*v+2) := by
    convert copyOn_executes g (1 : Fin 8) 5 7 (by decide) (by decide) (by decide) (store u v 0 0 u 0 []) rfl using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  obtain ⟨s,hs,hsb⟩ := split_executes g u v u v
  obtain ⟨t,ht,htb⟩ := choose_executes g u v
  refine ⟨_,seq_executes _ _ g h₀ (seq_executes _ _ g h₁ (seq_executes _ _ g hs ht)),?_⟩
  omega

lemma drop_queryFree : drop.QueryFree := by
  intro q a b next;fin_cases q <;> simp [drop,machine]
lemma finish_queryFree (source : Fin 2) : (finish source).QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ drop_queryFree (moveOn_queryFree _ _ _ _ _ _))
lemma split_queryFree : split.QueryFree := rename_queryFree _ _ CNFCloneEmitter.UnarySplit.program_queryFree
lemma reverseBranch_queryFree : reverseBranch.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ split_queryFree (seq_queryFree _ _ (clear_queryFree _) (finish_queryFree _))))
lemma program_queryFree : program.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ split_queryFree (branchPop_queryFree _ _ _ _ skip_queryFree (finish_queryFree _) reverseBranch_queryFree)))

noncomputable def on {k : ℕ} (φ : Fin 8 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 8 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k) (u v : ℕ)
    (hs : s∘φ=store u v 0 0 0 0 []) :
    ∃ c, (on φ).Executes g s
      (Function.update (Function.update s (φ 2) (List.replicate (min u v) true))
        (φ 3) (List.replicate (max u v-min u v-1) true)) c ∧ c≤50*(u+v+1) := by
  obtain ⟨c,hc,hb⟩ := program_executes g u v
  refine ⟨c,?_,hb⟩
  apply rename_executes_to program φ g hc hs
  · funext i
    have hi := congrFun hs i
    change s (φ i)=_ at hi
    simp only [Function.comp_def,Function.update_apply,φ.injective.eq_iff,hi]
    fin_cases i <;> rfl
  · intro i hi
    simp only [Function.update_of_ne (hi 2).symm,Function.update_of_ne (hi 3).symm]
lemma on_queryFree {k : ℕ} (φ : Fin 8 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ program_queryFree

end HiddenCircuits.Circuit.Runtime.EdgeEndpoints
