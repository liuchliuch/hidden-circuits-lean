import HiddenCircuits.Approximation.Initialization.NormalizeReversed
import HiddenCircuits.Approximation.SamplerRuntime.TapeRead
import HiddenCircuits.Complexity.BinaryArithmetic.WeightStreamsEmit

/-! Actual fixed-width fair-tape blocks become canonical unsigned
binary words. Missing bits are zero-padded, and the unused source is cleared. -/
namespace HiddenCircuits.Approximation.Initialization.TapeWords
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic SamplerRuntime

abbrev unary (n : ℕ) : BitString := List.replicate n true
def word (B : ℕ) (source : BitString) : BitString :=
  Computability.encodeNat (value (TapeRead.takePadded B source))
def words (B : ℕ) : ℕ → BitString → List BitString
  | 0,_ => []
  | q+1,source => word B source :: words B q (source.drop B)

theorem normalize_length (xs : BitString) : (normalize xs).length ≤ xs.length := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp only [BinaryArithmetic.normalize]; split_ifs <;> simp_all

theorem word_length (B : ℕ) (source : BitString) : (word B source).length ≤ B := by
  rw [word,←normalize_eq_encode]
  exact (normalize_length _).trans (by rw [TapeRead.prefix_length])

theorem encoded_length (B q : ℕ) (source : BitString) :
    (encodeBitList (words B q source)).length ≤ q*(2*B+2) := by
  induction q generalizing source with
  | zero => simp [words,encodeBitList]
  | succ q ih =>
    have hh := ih (source.drop B)
    have hl := word_length B source
    simp only [words,encodeBitList,List.length_cons,pairBits_length]
    nlinarith

def state (source : BitString) (B : ℕ) (clock acc counter rev output tmp : BitString) : Store 7 := fun r =>
  if r.val=0 then source else if r.val=1 then unary B else if r.val=2 then clock
  else if r.val=3 then acc else if r.val=4 then counter else if r.val=5 then rev
  else if r.val=6 then output else tmp
def scanState (source : BitString) (B q : ℕ) (acc : BitString) : Store 7 :=
  state source B (unary q) acc [] [] [] []

def readPorts : Fin 3 ↪ Fin 8 where
  toFun i := if i.val=0 then 0 else if i.val=1 then 4 else 5
  inj' := by decide +kernel
def normalizePorts : Fin 2 ↪ Fin 8 where
  toFun i := if i.val=0 then 5 else 6
  inj' := by decide +kernel
def emitPorts : Fin 2 ↪ Fin 8 where
  toFun i := if i.val=0 then 6 else 3
  inj' := by decide +kernel

noncomputable def body : OracleBlock 7 :=
  seq (copyOn 1 4 7 (by decide) (by decide) (by decide))
    (seq (TapeRead.on readPorts) (seq (rename NormalizeReversed.program normalizePorts)
      (rename wordEmit emitPorts)))
noncomputable def loop : OracleBlock 7 := whilePop 2 body body
noncomputable def program : OracleBlock 7 :=
  seq loop (seq (reverseOn 3 6 (by decide)) (clear 0))

theorem body_executes (g : BitString → ℕ) (source : BitString) (B q : ℕ) (acc : BitString) :
    ∃ t, body.Executes g (scanState source B q acc)
      (scanState (source.drop B) B q ((wordChunk (word B source)).reverse++acc)) t ∧
      t ≤ 19*B+20 := by
  let bs := TapeRead.takePadded B source
  have hc : (copyOn (1 : Fin 8) 4 7 (by decide) (by decide) (by decide)).Executes g
      (scanState source B q acc) (state source B (unary q) acc (unary B) [] [] []) (5*B+2) := by
    convert copyOn_executes g (1 : Fin 8) 4 7 (by decide) (by decide) (by decide)
      (scanState source B q acc) rfl using 1
    · funext r; fin_cases r <;> simp [state,scanState]
    · simp [state,scanState]
  have hr : (TapeRead.on readPorts).Executes g
      (state source B (unary q) acc (unary B) [] [] [])
      (state (source.drop B) B (unary q) acc [] bs.reverse [] []) (5*B+1) := by
    convert TapeRead.on_executes readPorts g
      (state source B (unary q) acc (unary B) [] [] [])
      (state (source.drop B) B (unary q) acc [] bs.reverse [] []) source (unary B) []
      (by funext r;fin_cases r <;> rfl)
      (by funext r;fin_cases r <;> simp [state,readPorts,TapeRead.state,bs])
      (by intro r hr;fin_cases r <;> first | rfl | exact (hr 0 rfl).elim | exact (hr 1 rfl).elim | exact (hr 2 rfl).elim) using 1
    simp
  obtain ⟨t,hn,hb⟩ := NormalizeReversed.canonical_executes g bs
  have hn' : (rename NormalizeReversed.program normalizePorts).Executes g
      (state (source.drop B) B (unary q) acc [] bs.reverse [] [])
      (state (source.drop B) B (unary q) acc [] [] (word B source) []) t := by
    apply rename_executes_to NormalizeReversed.program normalizePorts g hn
    · funext r;fin_cases r <;> rfl
    · funext r;fin_cases r <;> rfl
    · intro r hr;fin_cases r <;> first | rfl | exact (hr 0 rfl).elim | exact (hr 1 rfl).elim
  have he : (rename wordEmit emitPorts).Executes g
      (state (source.drop B) B (unary q) acc [] [] (word B source) [])
      (scanState (source.drop B) B q ((wordChunk (word B source)).reverse++acc))
      (6*(word B source).length+7) := by
    apply rename_executes_to wordEmit emitPorts g (wordEmit_executes g (word B source) acc)
    · funext r;fin_cases r <;> rfl
    · funext r;fin_cases r <;> rfl
    · intro r hr;fin_cases r <;> first | rfl | exact (hr 0 rfl).elim | exact (hr 1 rfl).elim
  refine ⟨_,seq_executes _ _ g hc (seq_executes _ _ g hr (seq_executes _ _ g hn' he)),?_⟩
  have hl := word_length B source
  simp only [bs,TapeRead.prefix_length] at hb
  omega

theorem pop_clock (source acc : BitString) (B q : ℕ) :
    Function.update (scanState source B (q+1) acc) 2 (unary q) = scanState source B q acc := by
  funext r;fin_cases r <;> rfl

theorem loop_execution (g : BitString → ℕ) (source : BitString) (B q : ℕ) (acc : BitString) :
    ∃ t, WhileExecution (2 : Fin 8) body body g (scanState source B q acc)
      (scanState (source.drop (q*B)) B 0 ((encodeBitList (words B q source)).reverse++acc)) t ∧
      t ≤ q*(19*B+22)+1 := by
  induction q generalizing source acc with
  | zero => exact ⟨1,by simpa [words,encodeBitList] using
      (WhileExecution.empty (stack := (2 : Fin 8)) (B := body) (C := body) (g := g)
        (scanState source B 0 acc) rfl),by simp⟩
  | succ q ih =>
    obtain ⟨a,ha,hab⟩ := body_executes g source B q acc
    obtain ⟨t,ht,hb⟩ := ih (source.drop B) ((wordChunk (word B source)).reverse++acc)
    have hh := WhileExecution.one (s := scanState source B (q+1) acc) (rest := unary q)
      (by rfl) (by rw [pop_clock];exact ha) ht
    refine ⟨1+a+1+t,?_,?_⟩
    · convert hh using 1 <;>
        simp [words,encodeBitList_eq_chunks,List.reverse_append,List.append_assoc,List.drop_drop,
          Nat.add_mul,Nat.add_comm]
    · nlinarith

theorem program_executes (g : BitString → ℕ) (source : BitString) (B q : ℕ) :
    ∃ t, program.Executes g (scanState source B q [])
      (state [] B [] [] [] [] (encodeBitList (words B q source)) []) t ∧
      t ≤ q*(23*B+26)+source.length+7 := by
  obtain ⟨a,ha,hab⟩ := loop_execution g source B q []
  simp only [List.append_nil] at ha
  have hr : (reverseOn (3 : Fin 8) 6 (by decide)).Executes g
      (scanState (source.drop (q*B)) B 0 (encodeBitList (words B q source)).reverse)
      (state (source.drop (q*B)) B [] [] [] [] (encodeBitList (words B q source)) [])
      (2*(encodeBitList (words B q source)).length+1) := by
    convert reverseOn_executes g (3 : Fin 8) 6 (by decide) _ using 1
    · funext r;fin_cases r <;> simp [state,scanState]
    · simp [state,scanState]
  have hc : (clear (0 : Fin 8)).Executes g
      (state (source.drop (q*B)) B [] [] [] [] (encodeBitList (words B q source)) [])
      (state [] B [] [] [] [] (encodeBitList (words B q source)) []) ((source.drop (q*B)).length+1) := by
    convert clear_executes g (0 : Fin 8) _ using 1
    funext r;fin_cases r <;> rfl
  refine ⟨_,seq_executes _ _ g (whilePop_executes _ _ _ g ha) (seq_executes _ _ g hr hc),?_⟩
  have hl := encoded_length B q source
  have hd : (source.drop (q*B)).length ≤ source.length := by simp
  nlinarith

theorem body_queryFree : body.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (TapeRead.on_queryFree _) (seq_queryFree _ _
    (rename_queryFree _ _ NormalizeReversed.program_queryFree) (rename_queryFree _ _ wordEmit_queryFree)))
theorem program_queryFree : program.QueryFree := seq_queryFree _ _
  (whilePop_queryFree _ _ _ body_queryFree body_queryFree)
  (seq_queryFree _ _ (reverseOn_queryFree _ _ _) (clear_queryFree _))

end HiddenCircuits.Approximation.Initialization.TapeWords
