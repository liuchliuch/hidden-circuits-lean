import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionScore

/-! The closed-neighborhood count is implemented by a fixed finite unary scan,
including initialization and cleanup, with an explicit cubic original-n bound. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRecognitionScore
open Complexity Complexity.OracleBlock DH.Runtime.PairCheck
open DH.Runtime.PairCheck.TestRuntime

noncomputable def loop : OracleBlock 22 := whilePop 7 body body
noncomputable def program : OracleBlock 22 :=
  seq (copyOn 0 7 19 (by decide) (by decide) (by decide))
    (seq loop (clear 6))

lemma pop_clock (n u x count : ℕ) (payload marks clock : BitString) (b : Bool) :
    Function.update (tallyState n u x count payload marks (b::clock)) (7 : Fin 23) clock =
      tallyState n u x count payload marks clock := by
  funext i;fin_cases i <;> rfl

lemma loop_execution (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (mask : Vector Bool n) (u : Fin n) (i m : ℕ) (him : i+m≤n) (count : ℕ) :
    ∃t, WhileExecution (7 : Fin 23) body body g
      (tallyState n u.val i count G.bits (liveBits mask) (List.replicate m true))
      (tallyState n u.val (i+m) (count+countFrom (hit G mask u) i m) G.bits (liveBits mask) []) t ∧
      t≤m*(330*(n+1)^2+2)+1 := by
  induction m generalizing i count with
  | zero =>
    exact ⟨1,by simpa [countFrom] using (WhileExecution.empty
      (stack := (7 : Fin 23)) (B := body) (C := body) (g := g)
      (tallyState n u.val i count G.bits (liveBits mask) []) rfl),by simp⟩
  | succ m ih =>
    have hi : i<n := by omega
    let x : Fin n := ⟨i,hi⟩
    obtain ⟨c,hc,hcb⟩ := body_executes g G mask u x count (List.replicate m true)
    obtain ⟨t,ht,htb⟩ := ih (i+1) (by omega) (count+if hit G mask u x then 1 else 0)
    have h := WhileExecution.one
      (show tallyState n u.val i count G.bits (liveBits mask) (List.replicate (m+1) true) 7 =
        true::List.replicate m true from rfl)
      (by simpa only [List.replicate_succ,pop_clock] using hc) ht
    refine ⟨1+c+1+t,?_,?_⟩
    · have he : i+1+m=i+(m+1) := by omega
      simpa only [countFrom,dif_pos hi,he,Nat.add_assoc] using h
    · nlinarith

/-- The count stack may contain an existing unary accumulator. Every other
public source is read-only; all private stacks return to empty. -/
theorem program_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (mask : Vector Bool n) (u : Fin n) (count : ℕ) :
    ∃t, program.Executes g (tallyState n u.val 0 count G.bits (liveBits mask) [])
      (tallyState n u.val 0 (count+score G mask u) G.bits (liveBits mask) []) t ∧
      t≤400*(n+1)^3 := by
  have hc : (copyOn (0 : Fin 23) 7 19 (by decide) (by decide) (by decide)).Executes g
      (tallyState n u.val 0 count G.bits (liveBits mask) [])
      (tallyState n u.val 0 count G.bits (liveBits mask) (List.replicate n true)) (5*n+2) := by
    convert copyOn_executes g (0 : Fin 23) 7 19 (by decide) (by decide) (by decide)
      (tallyState n u.val 0 count G.bits (liveBits mask) []) rfl using 1
    · funext i;fin_cases i <;> simp [tallyState,state,flags]
    · simp [tallyState,state,flags]
  obtain ⟨c,hh,hb⟩ := loop_execution g G mask u 0 n (by omega) count
  have hl : loop.Executes g
      (tallyState n u.val 0 count G.bits (liveBits mask) (List.replicate n true))
      (tallyState n u.val n (count+score G mask u) G.bits (liveBits mask) []) c := by
    simpa only [Nat.zero_add,score] using whilePop_executes _ _ _ g hh
  have hf : (clear (6 : Fin 23)).Executes g
      (tallyState n u.val n (count+score G mask u) G.bits (liveBits mask) [])
      (tallyState n u.val 0 (count+score G mask u) G.bits (liveBits mask) []) (n+1) := by
    convert clear_executes g (6 : Fin 23)
      (tallyState n u.val n (count+score G mask u) G.bits (liveBits mask) []) using 1
    · funext i;fin_cases i <;> rfl
    · simp [tallyState,state,flags]
  refine ⟨_,seq_executes _ _ g hc (seq_executes _ _ g hl hf),?_⟩
  nlinarith [Nat.zero_le (n^3),Nat.zero_le (n^2)]

lemma program_queryFree : program.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (whilePop_queryFree _ _ _ body_queryFree body_queryFree) (clear_queryFree _))

noncomputable def on {k : ℕ} (φ : Fin 23 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 23 ↪ Fin (k+1)) (g : BitString → ℕ)
    {n : ℕ} (G : MatrixData n) (mask : Vector Bool n) (u : Fin n) (count : ℕ) (s : Store k)
    (hs : s ∘ φ=tallyState n u.val 0 count G.bits (liveBits mask) []) :
    ∃t, (on φ).Executes g s (Function.update s (φ 5) (List.replicate (count+score G mask u) true)) t ∧
      t≤400*(n+1)^3 := by
  obtain ⟨t,ht,hb⟩ := program_executes g G mask u count
  refine ⟨t,?_,hb⟩
  apply rename_executes_to program φ g ht hs
  · have he : (Function.update s (φ 5) (List.replicate (count+score G mask u) true)) ∘ φ =
        Function.update (s ∘ φ) 5 (List.replicate (count+score G mask u) true) := by
      funext i;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i;fin_cases i <;> rfl
  · intro i hi
    exact Function.update_of_ne (hi 5).symm _ _

lemma on_queryFree {k : ℕ} (φ : Fin 23 ↪ Fin (k+1)) : (on φ).QueryFree :=
  rename_queryFree _ _ program_queryFree

lemma countFrom_le {n : ℕ} (f : Fin n → Bool) (i m : ℕ) : countFrom f i m≤m := by
  induction m generalizing i with
  | zero => simp [countFrom]
  | succ m ih =>
    have h := ih (i+1)
    simp only [countFrom]
    split <;> rename_i hh
    · split <;> omega
    · omega

lemma score_le {n : ℕ} (G : MatrixData n) (mask : Vector Bool n) (u : Fin n) : score G mask u≤n :=
  countFrom_le _ _ _

lemma countFrom_countP {n : ℕ} (f : Fin n → Bool) (i m : ℕ) :
    countFrom f i m=(List.range' i m).countP (fun j => if h:j<n then f ⟨j,h⟩ else false) := by
  induction m generalizing i with
  | zero => rfl
  | succ m ih =>
    simp only [countFrom,List.range'_succ,List.countP_cons,ih]
    split <;> rename_i hh
    · cases he : f ⟨i,hh⟩ <;> simp [he] <;> omega
    · simp

lemma score_countP {n : ℕ} (G : MatrixData n) (mask : Vector Bool n) (u : Fin n) :
    score G mask u=(List.finRange n).countP (hit G mask u) := by
  rw [score,countFrom_countP,←List.range_eq_range',←List.map_coe_finRange_eq_range,List.countP_map]
  apply List.countP_congr
  intro x hx
  simp only [Function.comp_def,dif_pos x.isLt]

end HiddenCircuits.GraphReduction.Runtime.UnitRecognitionScore
