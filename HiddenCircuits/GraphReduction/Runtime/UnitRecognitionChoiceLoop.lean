import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionChoiceBody

/-! A fixed finite-stack full-universe first-maximum scan. The work is bounded
by a quartic in the original vertex count, for every Boolean matrix and masks. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRecognitionChoice
open Complexity Complexity.OracleBlock DH.Runtime.PairCheck

def scanFrom {n : ℕ} (G : MatrixData n) (A S R : Vector Bool n) (i : ℕ) : ℕ → Best n → Best n
  | 0,b => b
  | m+1,b => if hi:i<n then scanFrom G A S R (i+1) m (step G A S R ⟨i,hi⟩ b) else b

def choose {n : ℕ} (G : MatrixData n) (A S R : Vector Bool n) : Best n := scanFrom G A S R 0 n none

noncomputable def loop : OracleBlock 32 := whilePop 10 body body
noncomputable def program : OracleBlock 32 :=
  seq (copyOn 0 10 15 (by decide) (by decide) (by decide)) (seq loop (clear 9))

lemma pop_clock {n : ℕ} (G : MatrixData n) (A S R : Vector Bool n) (b : Best n)
    (i : ℕ) (clock : BitString) (bit : Bool) :
    Function.update (state G A S R b i (bit::clock) [] [] [] []) (10 : Fin 33) clock=
      state G A S R b i clock [] [] [] [] := by
  funext j;fin_cases j <;> rfl

lemma loop_execution (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (A S R : Vector Bool n) (i m : ℕ) (him : i+m≤n) (b : Best n) :
    ∃t, WhileExecution (10 : Fin 33) body body g
      (state G A S R b i (List.replicate m true) [] [] [] [])
      (state G A S R (scanFrom G A S R i m b) (i+m) [] [] [] [] []) t ∧
      t≤m*(1500*(n+1)^3+2)+1 := by
  induction m generalizing i b with
  | zero =>
    exact ⟨1,by simpa only [scanFrom,Nat.add_zero] using (WhileExecution.empty
      (stack := (10 : Fin 33)) (B := body) (C := body) (g := g)
      (state G A S R b i [] [] [] [] []) rfl),by simp⟩
  | succ m ih =>
    have hi : i<n := by omega
    let x : Fin n := ⟨i,hi⟩
    obtain ⟨c,hc,hcb⟩ := body_executes g G A S R b x (List.replicate m true)
    obtain ⟨t,ht,htb⟩ := ih (i+1) (by omega) (step G A S R x b)
    have h := WhileExecution.one
      (show state G A S R b i (List.replicate (m+1) true) [] [] [] [] 10 =
        true::List.replicate m true from rfl)
      (by simpa only [List.replicate_succ,pop_clock] using hc) ht
    refine ⟨1+c+1+t,?_,?_⟩
    · have he : i+1+m=i+(m+1) := by omega
      simpa only [scanFrom,dif_pos hi,he] using h
    · nlinarith

/-- Every candidate, matrix access and comparison is evaluated by the literal
program; no ordering or runtime certificate is an input. -/
theorem program_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (A S R : Vector Bool n) :
    ∃t, program.Executes g (state G A S R none 0 [] [] [] [] [])
      (state G A S R (choose G A S R) 0 [] [] [] [] []) t ∧ t≤1600*(n+1)^4 := by
  have hc : (copyOn (0 : Fin 33) 10 15 (by decide) (by decide) (by decide)).Executes g
      (state G A S R none 0 [] [] [] [] [])
      (state G A S R none 0 (List.replicate n true) [] [] [] []) (5*n+2) := by
    convert copyOn_executes g (0 : Fin 33) 10 15 (by decide) (by decide) (by decide)
      (state G A S R none 0 [] [] [] [] []) rfl using 1
    · funext j;fin_cases j <;> simp [state,rawState]
    · simp [state,rawState]
  obtain ⟨c,h,hb⟩ := loop_execution g G A S R 0 n (by omega) none
  have hl : loop.Executes g (state G A S R none 0 (List.replicate n true) [] [] [] [])
      (state G A S R (choose G A S R) n [] [] [] [] []) c := by
    simpa only [choose,Nat.zero_add] using whilePop_executes _ _ _ g h
  have hf : (clear (9 : Fin 33)).Executes g (state G A S R (choose G A S R) n [] [] [] [] [])
      (state G A S R (choose G A S R) 0 [] [] [] [] []) (n+1) := by
    convert clear_executes g (9 : Fin 33) _ using 1
    · funext j;fin_cases j <;> rfl
    · simp [state,rawState]
  refine ⟨_,seq_executes _ _ g hc (seq_executes _ _ g hl hf),?_⟩
  nlinarith [Nat.zero_le (n^2),Nat.zero_le (n^3),Nat.zero_le (n^4)]

lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (whilePop_queryFree _ _ _ body_queryFree body_queryFree) (clear_queryFree _))

noncomputable def on {k : ℕ} (φ : Fin 33 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 33 ↪ Fin (k+1)) (g : BitString → ℕ)
    {n : ℕ} (G : MatrixData n) (A S R : Vector Bool n) (s t : Store k)
    (hs : s ∘ φ=state G A S R none 0 [] [] [] [] [])
    (ht : t ∘ φ=state G A S R (choose G A S R) 0 [] [] [] [] [])
    (hf : ∀r,(∀j,φ j≠r) → t r=s r) :
    ∃c, (on φ).Executes g s t c ∧ c≤1600*(n+1)^4 := by
  obtain ⟨c,h,hb⟩ := program_executes g G A S R
  exact ⟨c,rename_executes_to program φ g h hs ht hf,hb⟩

lemma on_queryFree {k : ℕ} (φ : Fin 33 ↪ Fin (k+1)) : (on φ).QueryFree :=
  rename_queryFree _ _ program_queryFree

end HiddenCircuits.GraphReduction.Runtime.UnitRecognitionChoice
