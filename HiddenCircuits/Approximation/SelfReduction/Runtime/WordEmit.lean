import HiddenCircuits.Approximation.SelfReduction.Runtime.PairEmit

/-! A dynamic arbitrary-word serializer for actual sampler outputs. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

noncomputable def emitReversedBit {k : ℕ} (output : Fin (k+1)) (b : Bool) : OracleBlock k :=
  seq (push output true) (push output b)
noncomputable def emitReversedPayload {k : ℕ} (source output : Fin (k+1)) : OracleBlock k :=
  whilePop source (emitReversedBit output false) (emitReversedBit output true)
noncomputable def emitWordReversed {k : ℕ} (source output : Fin (k+1)) : OracleBlock k :=
  seq (push output true) (seq (emitReversedPayload source output) (push output false))

 theorem emitReversedBit_executes {k : ℕ} (g : BitString → ℕ) (output : Fin (k+1)) (b : Bool) (s : Store k) :
    (emitReversedBit output b).Executes g s (Function.update s output (b::true::s output)) 4 := by
  have h1 := push_executes g output true s
  have h2 := push_executes g output b (Function.update s output (true::s output))
  simpa only [Function.update_self,Function.update_idem] using seq_executes _ _ g h1 h2

 theorem emitReversedPayload_execution {k : ℕ} (g : BitString → ℕ) (source output : Fin (k+1))
    (hne : source ≠ output) (s : Store k) (xs acc : BitString) :
    WhileExecution source (emitReversedBit output false) (emitReversedBit output true) g
      (workStore s source output xs acc)
      (workStore s source output [] ((escapedBits xs).reverse ++ acc)) (6*xs.length+1) := by
  induction xs generalizing acc with
  | nil => exact WhileExecution.empty _ (workStore_counter _ _ _ hne _ _)
  | cons b xs ih =>
    have hb : (emitReversedBit output b).Executes g
        (Function.update (workStore s source output (b::xs) acc) source xs)
        (workStore s source output xs (b::true::acc)) 4 := by
      rw [workStore_pop _ _ _ hne]
      simpa [workStore] using emitReversedBit_executes g output b (workStore s source output xs acc)
    have hs := workStore_counter s source output hne (b::xs) acc
    have h : WhileExecution source (emitReversedBit output false) (emitReversedBit output true) g
        (workStore s source output (b::xs) acc)
        (workStore s source output [] ((escapedBits xs).reverse ++ b::true::acc)) (1+4+1+(6*xs.length+1)) := by
      cases b
      · exact WhileExecution.zero hs hb (ih _)
      · exact WhileExecution.one hs hb (ih _)
    convert h using 1
    · simp [escapedBits,List.reverse_append,List.append_assoc]
    · simp; omega

 theorem emitReversedPayload_executes {k : ℕ} (g : BitString → ℕ) (source output : Fin (k+1))
    (hne : source ≠ output) (s : Store k) :
    (emitReversedPayload source output).Executes g s
      (Function.update (Function.update s source []) output ((escapedBits (s source)).reverse ++ s output))
      (6*(s source).length+1) := by
  simpa [workStore] using whilePop_executes _ _ _ g
    (emitReversedPayload_execution g source output hne s (s source) (s output))

 theorem emitWordReversed_executes {k : ℕ} (g : BitString → ℕ) (source output : Fin (k+1))
    (hne : source ≠ output) (s : Store k) :
    (emitWordReversed source output).Executes g s
      (Function.update (Function.update s source []) output
        ((true::pairBits (s source) []).reverse ++ s output)) (6*(s source).length+7) := by
  let s1 := Function.update s output (true::s output)
  have h1 : (push output true).Executes g s s1 1 := push_executes g output true s
  have h2 := emitReversedPayload_executes g source output hne s1
  let s2 := Function.update (Function.update s1 source []) output ((escapedBits (s1 source)).reverse ++ s1 output)
  have h3 := push_executes g output false s2
  have h := seq_executes _ _ g h1 (seq_executes _ _ g h2 h3)
  convert h using 1
  · funext i
    by_cases hi : i=output
    · subst i
      simp [s1,s2,hne,pairBits_eq_escaped,List.reverse_cons,List.reverse_append,List.append_assoc]
    · by_cases hs : i=source
      · subst i; simp [s1,s2,hne]
      · simp [s1,s2,hi,hs]
  · simp [s1,hne]
    omega

 theorem emitWordReversed_queryFree {k : ℕ} (source output : Fin (k+1)) :
    (emitWordReversed source output).QueryFree :=
  seq_queryFree _ _ (push_queryFree _ _) (seq_queryFree _ _
    (whilePop_queryFree _ _ _ (seq_queryFree _ _ (push_queryFree _ _) (push_queryFree _ _))
      (seq_queryFree _ _ (push_queryFree _ _) (push_queryFree _ _))) (push_queryFree _ _))

end HiddenCircuits.Approximation.SelfReduction.Runtime
