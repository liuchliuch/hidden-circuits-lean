import HiddenCircuits.Circuit.Runtime.SamplePairParser
import HiddenCircuits.Complexity.PolynomialBounds

/-! Actual linear-time unary length of a canonical self-delimiting word array. -/
namespace HiddenCircuits.Circuit.Runtime.WordCount
open HiddenCircuits.Complexity OracleBlock Polynomial

def store (input stream atom : BitString) (count : ℕ) : Store 5 := fun i =>
  if i.val=0 then input else if i.val=1 then stream else if i.val=2 then atom
  else if i.val=5 then List.replicate count true else []
def parseEmbedding : Fin 4 ↪ Fin 6 where
  toFun i := (![1,2,3,4] : Fin 4 → Fin 6) i
  inj' := by decide +kernel
noncomputable def body : OracleBlock 5 := seq (SamplePairParser.on parseEmbedding) (seq (clear 2) (push 5 true))
noncomputable def loop : OracleBlock 5 := whilePop 1 body body
noncomputable def program : OracleBlock 5 := seq (copyOn 0 1 3 (by decide) (by decide) (by decide)) loop
noncomputable def time : Polynomial ℕ := 13*X+5

theorem body_executes (g : BitString → ℕ) (input word rest : BitString) (count : ℕ) :
    body.Executes g (store input (pairBits word rest) [] count) (store input rest [] (count+1)) (6*word.length+13) := by
  have hp : (SamplePairParser.on parseEmbedding).Executes g (store input (pairBits word rest) [] count)
      (store input rest word count) (5*word.length+7) := by
    apply SamplePairParser.on_executes parseEmbedding g word rest
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim
  have hc : (clear (2:Fin 6)).Executes g (store input rest word count) (store input rest [] count) (word.length+1) := by
    convert clear_executes g (2:Fin 6) (store input rest word count) using 1
    funext i;fin_cases i <;> rfl
  have hi : (push (5:Fin 6) true).Executes g (store input rest [] count) (store input rest [] (count+1)) 1 := by
    convert push_executes g (5:Fin 6) true (store input rest [] count) using 1
    funext i;fin_cases i <;> simp [store,List.replicate_succ]
  convert seq_executes _ _ g hp (seq_executes _ _ g hc hi) using 1 <;> omega

theorem loop_execution (g : BitString → ℕ) (input : BitString) (ws : List BitString) (count : ℕ) :
    ∃c,WhileExecution (1:Fin 6) body body g (store input (encodeBitList ws) [] count)
      (store input [] [] (count+ws.length)) c ∧ c≤8*(encodeBitList ws).length+1 := by
  induction ws generalizing count with
  | nil => exact ⟨1,by simpa using WhileExecution.empty (store input [] [] count) rfl,by simp [encodeBitList]⟩
  | cons w ws ih =>
    obtain ⟨c,h,hb⟩ := ih (count+1)
    have hu : Function.update (store input (encodeBitList (w::ws)) [] count) 1 (pairBits w (encodeBitList ws))=
        store input (pairBits w (encodeBitList ws)) [] count := by funext i;fin_cases i <;> rfl
    have hh := WhileExecution.one (stack:=(1:Fin 6)) (B:=body) (C:=body) (g:=g) rfl
      (by rw [hu];exact body_executes g input w (encodeBitList ws) count) h
    refine ⟨1+(6*w.length+13)+1+c,?_,?_⟩
    · simpa only [List.length_cons,show count+1+ws.length=count+(ws.length+1) by omega] using hh
    · simp only [encodeBitList,List.length_cons,pairBits_length]
      omega

theorem program_executes (g : BitString → ℕ) (ws : List BitString) :
    ∃c,program.Executes g (store (encodeBitList ws) [] [] 0) (store (encodeBitList ws) [] [] ws.length) c ∧
      c≤time.eval (encodeBitList ws).length := by
  have hc : (copyOn (0:Fin 6) 1 3 (by decide) (by decide) (by decide)).Executes g
      (store (encodeBitList ws) [] [] 0) (store (encodeBitList ws) (encodeBitList ws) [] 0) (5*(encodeBitList ws).length+2) := by
    convert copyOn_executes g (0:Fin 6) 1 3 (by decide) (by decide) (by decide) (store (encodeBitList ws) [] [] 0) rfl using 1
    funext i;fin_cases i <;> simp [store]
  obtain ⟨c,h,hb⟩ := loop_execution g (encodeBitList ws) ws 0
  simp only [Nat.zero_add] at h
  refine ⟨_,seq_executes _ _ g hc (whilePop_executes _ _ _ g h),?_⟩
  simp only [time,eval_add,eval_mul,eval_X,eval_ofNat]
  omega

lemma body_queryFree : body.QueryFree := seq_queryFree _ _ (SamplePairParser.on_queryFree _) (seq_queryFree _ _ (clear_queryFree _) (push_queryFree _ _))
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (whilePop_queryFree _ _ _ body_queryFree body_queryFree)

noncomputable def on {k : ℕ} (φ : Fin 6 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 6 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k) (ws : List BitString)
    (hs : s∘φ=store (encodeBitList ws) [] [] 0) :
    ∃c,(on φ).Executes g s (Function.update s (φ 5) (List.replicate ws.length true)) c ∧ c≤time.eval (encodeBitList ws).length := by
  obtain ⟨c,h,hb⟩ := program_executes g ws
  refine ⟨c,?_,hb⟩
  apply rename_executes_to program φ g h hs
  · funext q
    simp only [Function.comp_apply,Function.update_apply,φ.injective.eq_iff]
    have hq := congrFun hs q
    change s (φ q)=_ at hq
    rw [hq]
    fin_cases q <;> rfl
  · intro q hq;simp only [Function.update_of_ne (hq 5).symm]
lemma on_queryFree {k : ℕ} (φ : Fin 6 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ program_queryFree

end HiddenCircuits.Circuit.Runtime.WordCount
