import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionRootsBody

/-! Bounded first-success all-root enumeration. Only n original labels are
tried; each component trial is polynomially bounded and uses adjacency only. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRecognitionRoots
open Complexity Complexity.OracleBlock DH.Runtime.PairCheck

def scanFrom {n : ℕ} (G : MatrixData n) (A : Vector Bool n) (i : ℕ) : ℕ → Best n → Best n
  | 0,b => b
  | m+1,b => if hi:i<n then scanFrom G A (i+1) m (step G A ⟨i,hi⟩ b) else b

def find {n : ℕ} (G : MatrixData n) (A : Vector Bool n) : Best n := scanFrom G A 0 n none

noncomputable def loop : OracleBlock 42 := whilePop 40 body body
noncomputable def program : OracleBlock 42 := seq
  (copyOn 0 40 15 (by decide) (by decide) (by decide)) (seq loop (clear 39))

lemma pop_clock {n : ℕ} (G : MatrixData n) (A : Vector Bool n) (b : Best n) (i : ℕ)
    (clock : BitString) (bit : Bool) :
    Function.update (state G A b i none (bit::clock) [] [] [] [] []) (40 : Fin 43) clock=
      state G A b i none clock [] [] [] [] [] := by
  funext j;fin_cases j <;> rfl

theorem loop_execution (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (A : Vector Bool n) (i m : ℕ) (him : i+m≤n) (b : Best n) :
    ∃t, WhileExecution (40 : Fin 43) body body g
      (state G A b i none (List.replicate m true) [] [] [] [] [])
      (state G A (scanFrom G A i m b) (i+m) none [] [] [] [] [] []) t ∧
      t≤m*(11000*(n+1)^5+2)+1 := by
  induction m generalizing i b with
  | zero => exact ⟨1,by simpa only [scanFrom,Nat.add_zero] using
      (WhileExecution.empty (stack := (40 : Fin 43)) (B := body) (C := body) (g := g)
        (state G A b i none [] [] [] [] [] []) rfl),by simp⟩
  | succ m ih =>
    have hi : i<n := by omega
    let x : Fin n := ⟨i,hi⟩
    obtain ⟨c,hc,hcb⟩ := body_executes g G A b x (List.replicate m true)
    obtain ⟨t,ht,htb⟩ := ih (i+1) (by omega) (step G A x b)
    have h := WhileExecution.one
      (show state G A b i none (List.replicate (m+1) true) [] [] [] [] [] 40 = true::List.replicate m true from rfl)
      (by simpa only [List.replicate_succ,pop_clock] using hc) ht
    refine ⟨1+c+1+t,?_,?_⟩
    · have he : i+1+m=i+(m+1) := by omega
      simpa only [scanFrom,dif_pos hi,he] using h
    · nlinarith

theorem program_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n) (A : Vector Bool n) :
    ∃t, program.Executes g (state G A none 0 none [] [] [] [] [] [])
      (state G A (find G A) 0 none [] [] [] [] [] []) t ∧ t≤12000*(n+1)^6 := by
  have h1 : (copyOn (0 : Fin 43) 40 15 (by decide) (by decide) (by decide)).Executes g
      (state G A none 0 none [] [] [] [] [] [])
      (state G A none 0 none (List.replicate n true) [] [] [] [] []) (5*n+2) := by
    convert copyOn_executes g (0 : Fin 43) 40 15 (by decide) (by decide) (by decide)
      (state G A none 0 none [] [] [] [] [] []) rfl using 1
    · funext j;fin_cases j <;> simp [state,UnitRecognitionComponent.store,UnitRecognitionChoice.rawState]
    · simp [state,UnitRecognitionComponent.store,UnitRecognitionChoice.rawState]
  obtain ⟨c,h2,b2⟩ := loop_execution g G A 0 n (by omega) none
  simp only [Nat.zero_add] at h2
  have h3 : (clear (39 : Fin 43)).Executes g (state G A (find G A) n none [] [] [] [] [] [])
      (state G A (find G A) 0 none [] [] [] [] [] []) (n+1) := by
    convert clear_executes g (39 : Fin 43) _ using 1
    · funext j;fin_cases j <;> rfl
    · simp [state]
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g (whilePop_executes _ _ _ g h2) h3),?_⟩
  nlinarith [Nat.zero_le (n^2),Nat.zero_le (n^3),Nat.zero_le (n^4),Nat.zero_le (n^5),Nat.zero_le (n^6)]

lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (whilePop_queryFree _ _ _ body_queryFree body_queryFree) (clear_queryFree _))

end HiddenCircuits.GraphReduction.Runtime.UnitRecognitionRoots
