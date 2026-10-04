import HiddenCircuits.Complexity.OracleLibrary
import HiddenCircuits.Complexity.OracleBlockNoQuery

/-! Fixed-width random-tape consumption. Missing raw-input bits are zero-padded;
canonical random tapes are consumed exactly, with no probabilistic retries. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.TapeRead
open Complexity Complexity.OracleBlock

def takePadded : ℕ → BitString → BitString
  | 0,_ => []
  | n+1,xs => xs.headD false :: takePadded n xs.tail

def state (source clock result : BitString) : Store 2 := fun i =>
  if i.val=0 then source else if i.val=1 then clock else result
noncomputable def body : OracleBlock 2 := branchPop 0 (push 2 false) (push 2 false) (push 2 true)
noncomputable def program : OracleBlock 2 := whilePop 1 body body

lemma body_executes (g : BitString → ℕ) (source clock result : BitString) :
    body.Executes g (state source clock result)
      (state source.tail clock (source.headD false::result)) 3 := by
  cases source with
  | nil =>
    apply branchPop_empty _ _ _ _ g rfl
    convert push_executes g (2:Fin 3) false (state [] clock result) using 1
    funext r;fin_cases r <;> rfl
  | cons b source =>
    have hp : (push (2:Fin 3) b).Executes g
        (Function.update (state (b::source) clock result) 0 source)
        (state source clock (b::result)) 1 := by
      convert push_executes g (2:Fin 3) b (state source clock result) using 1
      · funext r;fin_cases r <;> rfl
      · funext r;fin_cases r <;> rfl
    cases b
    · exact branchPop_false _ _ _ _ g rfl hp
    · exact branchPop_true _ _ _ _ g rfl hp

lemma pop_clock (source clock result : BitString) (b : Bool) :
    Function.update (state source (b::clock) result) 1 clock=state source clock result := by
  funext r;fin_cases r <;> rfl

lemma tail_drop (source : BitString) (n : ℕ) : source.tail.drop n=source.drop (n+1) := by
  cases source <;> simp

/-- A literal tape extractor executes exactly five instructions per requested
bit and one terminating clock test, on every raw source and clock. -/
theorem program_executes (g : BitString → ℕ) (source clock result : BitString) :
    program.Executes g (state source clock result)
      (state (source.drop clock.length) [] ((takePadded clock.length source).reverse++result))
      (5*clock.length+1) := by
  apply whilePop_executes
  induction clock generalizing source result with
  | nil => simpa [takePadded] using (WhileExecution.empty (stack:=(1:Fin 3)) (B:=body) (C:=body)
      (g:=g) (state source [] result) rfl)
  | cons b clock ih =>
    have hb := body_executes g source clock result
    have hh : WhileExecution (1:Fin 3) body body g (state source (b::clock) result)
        (state (source.tail.drop clock.length) []
          ((takePadded clock.length source.tail).reverse++(source.headD false::result)))
        (1+3+1+(5*clock.length+1)) := by
      cases b
      · exact WhileExecution.zero rfl (by rw [pop_clock];exact hb) (ih _ _)
      · exact WhileExecution.one rfl (by rw [pop_clock];exact hb) (ih _ _)
    convert hh using 1
    · simp [takePadded,tail_drop,List.reverse_cons,List.append_assoc]
    · simp;omega

lemma prefix_length (n : ℕ) (xs : BitString) : (takePadded n xs).length=n := by
  induction n generalizing xs <;> simp_all [takePadded]

lemma prefix_eq_take (n : ℕ) (xs : BitString) (h : n≤xs.length) : takePadded n xs=xs.take n := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    cases xs with
    | nil => simp at h
    | cons b xs => simp only [takePadded,List.headD_cons,List.tail_cons,List.take_succ_cons];rw [ih xs (by simpa using h)]

lemma program_queryFree : program.QueryFree := whilePop_queryFree _ _ _
  (branchPop_queryFree _ _ _ _ (push_queryFree _ _) (push_queryFree _ _) (push_queryFree _ _))
  (branchPop_queryFree _ _ _ _ (push_queryFree _ _) (push_queryFree _ _) (push_queryFree _ _))

noncomputable def on {k : ℕ} (φ : Fin 3 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 3 ↪ Fin (k+1)) (g : BitString → ℕ)
    (s t : Store k) (source clock result : BitString)
    (hs : s∘φ=state source clock result)
    (ht : t∘φ=state (source.drop clock.length) [] ((takePadded clock.length source).reverse++result))
    (hf : ∀r,(∀j,φ j≠r) → t r=s r) :
    (on φ).Executes g s t (5*clock.length+1) :=
  rename_executes_to program φ g (program_executes g source clock result) hs ht hf

lemma on_queryFree {k : ℕ} (φ : Fin 3 ↪ Fin (k+1)) : (on φ).QueryFree :=
  rename_queryFree _ _ program_queryFree

end HiddenCircuits.Approximation.SamplerRuntime.TapeRead
