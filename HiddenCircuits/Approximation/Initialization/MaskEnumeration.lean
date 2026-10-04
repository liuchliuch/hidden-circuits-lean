import HiddenCircuits.Approximation.Initialization.MaskData
import HiddenCircuits.Approximation.SamplerRuntime.Identity

/-! A literal seven-stack retained-vertex enumerator. It preserves
the mask, emits increasing unary vertex addresses, and counts selected bits. -/
namespace HiddenCircuits.Approximation.Initialization.MaskEnumeration
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic SamplerRuntime

abbrev unary (i : ℕ) : BitString := List.replicate i true

def indices (i : ℕ) : BitString → List ℕ
  | [] => []
  | b::bs => if b then i :: indices (i+1) bs else indices (i+1) bs

def words (i : ℕ) (mask : BitString) : List BitString := (indices i mask).map unary

theorem words_nil (i : ℕ) : words i [] = [] := rfl
theorem words_false (i : ℕ) (bs : BitString) : words i (false::bs) = words (i+1) bs := rfl
theorem words_true (i : ℕ) (bs : BitString) : words i (true::bs) = unary i :: words (i+1) bs := rfl

theorem encoded_length (i : ℕ) (mask : BitString) :
    (encodeBitList (words i mask)).length ≤ mask.length*(2*i+mask.length+1) := by
  induction mask generalizing i with
  | nil => simp [words,indices,encodeBitList]
  | cons b bs ih =>
    have hh := ih (i+1)
    cases b <;> simp only [words_false,words_true,encodeBitList,List.length_cons,
      pairBits_length,List.length_replicate] <;> nlinarith

def state (input count acc scan index temporary word : BitString) : Store 6 := fun r =>
  if r.val=0 then input else if r.val=1 then count else if r.val=2 then acc
  else if r.val=3 then scan else if r.val=4 then index else if r.val=5 then temporary else word

def scanState (input : BitString) (count : ℕ) (acc scan : BitString) (index : ℕ) : Store 6 :=
  state input (unary count) acc scan (unary index) [] []

def identityPorts : Fin 6 ↪ Fin 7 where
  toFun i := if i.val=0 then 0 else ⟨i.val+1,by omega⟩
  inj' := by decide +kernel

noncomputable def trueBody : OracleBlock 6 :=
  seq (rename Identity.body identityPorts) (push 1 true)
noncomputable def falseBody : OracleBlock 6 := push 4 true
noncomputable def loop : OracleBlock 6 := whilePop 3 falseBody trueBody
noncomputable def finish : OracleBlock 6 := seq (clear 4) (reverseOn 2 4 (by decide))
noncomputable def program : OracleBlock 6 :=
  seq (copyOn 0 3 5 (by decide) (by decide) (by decide)) (seq loop finish)

theorem trueBody_executes (g : BitString → ℕ) (input scan acc : BitString) (c i : ℕ) :
    trueBody.Executes g (scanState input c acc scan i)
      (scanState input (c+1) ((wordChunk (unary i)).reverse++acc) scan (i+1)) (11*i+17) := by
  have hb : (rename Identity.body identityPorts).Executes g (scanState input c acc scan i)
      (scanState input c ((wordChunk (unary i)).reverse++acc) scan (i+1)) (11*i+14) := by
    apply rename_executes_to Identity.body identityPorts g (Identity.body_executes g input acc scan i)
    · funext r; fin_cases r <;> rfl
    · funext r; fin_cases r <;> rfl
    · intro r hr
      fin_cases r
      all_goals first | rfl | exact (hr 0 rfl).elim | exact (hr 1 rfl).elim |
        exact (hr 2 rfl).elim | exact (hr 3 rfl).elim | exact (hr 4 rfl).elim | exact (hr 5 rfl).elim
  have hp : (push (1 : Fin 7) true).Executes g
      (scanState input c ((wordChunk (unary i)).reverse++acc) scan (i+1))
      (scanState input (c+1) ((wordChunk (unary i)).reverse++acc) scan (i+1)) 1 := by
    convert push_executes g (1 : Fin 7) true _ using 1
    funext r; fin_cases r <;> simp [scanState,state,unary,List.replicate_succ]
  convert seq_executes _ _ g hb hp using 1 <;> omega

theorem falseBody_executes (g : BitString → ℕ) (input scan acc : BitString) (c i : ℕ) :
    falseBody.Executes g (scanState input c acc scan i) (scanState input c acc scan (i+1)) 1 := by
  convert push_executes g (4 : Fin 7) true _ using 1
  funext r; fin_cases r <;> simp [scanState,state,unary,List.replicate_succ]

theorem pop_scan (input acc scan : BitString) (c i : ℕ) (b : Bool) :
    Function.update (scanState input c acc (b::scan) i) 3 scan = scanState input c acc scan i := by
  funext r; fin_cases r <;> rfl

theorem loop_execution (g : BitString → ℕ) (input scan acc : BitString) (c i : ℕ) :
    ∃ t, WhileExecution (3 : Fin 7) falseBody trueBody g (scanState input c acc scan i)
      (scanState input (c+scan.count true) ((encodeBitList (words i scan)).reverse++acc)
        [] (i+scan.length)) t ∧ t ≤ 16*scan.length*(i+scan.length+1)+1 := by
  induction scan generalizing c i acc with
  | nil =>
    exact ⟨1,by simpa [words_nil,encodeBitList] using
      (WhileExecution.empty (stack := (3 : Fin 7)) (B := falseBody) (C := trueBody)
        (g := g) (scanState input c acc [] i) rfl),by simp⟩
  | cons b bs ih =>
    cases b with
    | false =>
      obtain ⟨t,ht,hb⟩ := ih acc c (i+1)
      have hh := WhileExecution.zero (s := scanState input c acc (false::bs) i)
        (rest := bs) rfl (by rw [pop_scan]; exact falseBody_executes g input bs acc c i) ht
      refine ⟨1+1+1+t,?_,?_⟩
      · convert hh using 1 <;> simp [words_false,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      · simp only [List.length_cons]; nlinarith
    | true =>
      obtain ⟨t,ht,hb⟩ := ih ((wordChunk (unary i)).reverse++acc) (c+1) (i+1)
      have hh := WhileExecution.one (s := scanState input c acc (true::bs) i)
        (rest := bs) rfl (by rw [pop_scan]; exact trueBody_executes g input bs acc c i) ht
      refine ⟨1+(11*i+17)+1+t,?_,?_⟩
      · convert hh using 1 <;>
          simp [words_true,encodeBitList_eq_chunks,List.reverse_append,List.append_assoc,
            Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      · simp only [List.length_cons]; nlinarith

theorem program_executes (g : BitString → ℕ) (mask : BitString) :
    ∃ t, program.Executes g (state mask [] [] [] [] [] [])
      (state mask (unary (mask.count true)) [] [] (encodeBitList (words 0 mask)) [] []) t ∧
      t ≤ 55*(mask.length+1)^2 := by
  have hc : (copyOn (0 : Fin 7) 3 5 (by decide) (by decide) (by decide)).Executes g
      (state mask [] [] [] [] [] []) (scanState mask 0 [] mask 0) (5*mask.length+2) := by
    convert copyOn_executes g (0 : Fin 7) 3 5 (by decide) (by decide) (by decide)
      (state mask [] [] [] [] [] []) rfl using 1
    funext r; fin_cases r <;> simp [state,scanState]
  obtain ⟨t,ht,hb⟩ := loop_execution g mask mask [] 0 0
  simp only [Nat.zero_add,List.append_nil] at ht hb
  have hclear : (clear (4 : Fin 7)).Executes g
      (scanState mask (mask.count true) (encodeBitList (words 0 mask)).reverse [] mask.length)
      (scanState mask (mask.count true) (encodeBitList (words 0 mask)).reverse [] 0) (mask.length+1) := by
    convert clear_executes g (4 : Fin 7) _ using 1
    · funext r; fin_cases r <;> simp [state,scanState]
    · simp [state,scanState]
  have hrev : (reverseOn (2 : Fin 7) 4 (by decide)).Executes g
      (scanState mask (mask.count true) (encodeBitList (words 0 mask)).reverse [] 0)
      (state mask (unary (mask.count true)) [] [] (encodeBitList (words 0 mask)) [] [])
      (2*(encodeBitList (words 0 mask)).length+1) := by
    convert reverseOn_executes g (2 : Fin 7) 4 (by decide) _ using 1
    · funext r; fin_cases r <;> simp [state,scanState]
    · simp [state,scanState]
  refine ⟨_,seq_executes _ _ g hc (seq_executes _ _ g (whilePop_executes _ _ _ g ht)
    (seq_executes _ _ g hclear hrev)),?_⟩
  have hl := encoded_length 0 mask
  nlinarith

theorem program_queryFree : program.QueryFree := by
  have htrue : trueBody.QueryFree := seq_queryFree _ _
    (rename_queryFree _ _ Identity.body_queryFree) (push_queryFree _ _)
  exact seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (whilePop_queryFree _ _ _ (push_queryFree _ _) htrue)
      (seq_queryFree _ _ (clear_queryFree _) (reverseOn_queryFree _ _ _)))

end HiddenCircuits.Approximation.Initialization.MaskEnumeration
