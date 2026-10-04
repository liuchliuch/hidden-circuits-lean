import HiddenCircuits.Complexity.OracleRepeat

/-! Actual dynamic binary pairing and word-list serialization. No uncharged
encoding operation is used inside the sampling loop. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

def escapedBits (xs : BitString) : BitString := xs.flatMap (fun b => [true,b])

 theorem pairBits_eq_escaped (xs ys : BitString) : pairBits xs ys=escapedBits xs ++ false::ys := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [pairBits,escapedBits,ih]

noncomputable def emitEscapedBit {k : ℕ} (output : Fin (k+1)) (b : Bool) : OracleBlock k :=
  seq (push output b) (push output true)
noncomputable def emitEscaped {k : ℕ} (source output : Fin (k+1)) : OracleBlock k :=
  whilePop source (emitEscapedBit output false) (emitEscapedBit output true)

 theorem emitEscapedBit_executes {k : ℕ} (g : BitString → ℕ) (output : Fin (k+1)) (b : Bool) (s : Store k) :
    (emitEscapedBit output b).Executes g s (Function.update s output (true::b::s output)) 4 := by
  have h1 := push_executes g output b s
  have h2 := push_executes g output true (Function.update s output (b::s output))
  simpa only [Function.update_self, Function.update_idem] using seq_executes _ _ g h1 h2

 theorem emitEscaped_execution {k : ℕ} (g : BitString → ℕ) (source output : Fin (k+1))
    (hne : source ≠ output) (s : Store k) (xs acc : BitString) :
    WhileExecution source (emitEscapedBit output false) (emitEscapedBit output true) g
      (workStore s source output xs acc)
      (workStore s source output [] (escapedBits xs.reverse ++ acc)) (6*xs.length+1) := by
  induction xs generalizing acc with
  | nil => exact WhileExecution.empty _ (workStore_counter _ _ _ hne _ _)
  | cons b xs ih =>
    have hb : (emitEscapedBit output b).Executes g
        (Function.update (workStore s source output (b::xs) acc) source xs)
        (workStore s source output xs (true::b::acc)) 4 := by
      rw [workStore_pop _ _ _ hne]
      simpa [workStore] using emitEscapedBit_executes g output b (workStore s source output xs acc)
    have hs := workStore_counter s source output hne (b::xs) acc
    have h : WhileExecution source (emitEscapedBit output false) (emitEscapedBit output true) g
        (workStore s source output (b::xs) acc)
        (workStore s source output [] (escapedBits xs.reverse ++ true::b::acc)) (1+4+1+(6*xs.length+1)) := by
      cases b
      · exact WhileExecution.zero hs hb (ih _)
      · exact WhileExecution.one hs hb (ih _)
    convert h using 1
    · simp [escapedBits,List.reverse_cons,List.flatMap_append,List.append_assoc]
    · simp; omega

 theorem emitEscaped_executes {k : ℕ} (g : BitString → ℕ) (source output : Fin (k+1))
    (hne : source ≠ output) (s : Store k) :
    (emitEscaped source output).Executes g s
      (Function.update (Function.update s source []) output (escapedBits (s source).reverse ++ s output))
      (6*(s source).length+1) := by
  simpa [workStore] using whilePop_executes _ _ _ g
    (emitEscaped_execution g source output hne s (s source) (s output))

noncomputable def pairEmit {k : ℕ} (source output temp : Fin (k+1))
    (hst : source ≠ temp) (htu : temp ≠ output) : OracleBlock k :=
  seq (reverseOn source temp hst) (seq (push output false) (emitEscaped temp output))

/-- Pair the runtime source word with the runtime suffix already on the output
stack, preserving every other port and clearing both scratch/source ports. -/
theorem pairEmit_executes {k : ℕ} (g : BitString → ℕ) (source output temp : Fin (k+1))
    (hso : source ≠ output) (hst : source ≠ temp) (hto : temp ≠ output)
    (s : Store k) (ht : s temp=[]) :
    (pairEmit source output temp hst hto).Executes g s
      (Function.update (Function.update s source []) output (pairBits (s source) (s output)))
      (8*(s source).length+7) := by
  let s1 := Function.update (Function.update s source []) temp (s source).reverse
  have h1 : (reverseOn source temp hst).Executes g s s1 (2*(s source).length+1) := by
    simpa [s1,ht,Function.update_comm hst] using reverseOn_executes g source temp hst s
  let s2 := Function.update s1 output (false::s output)
  have h2 : (push output false).Executes g s1 s2 1 := by
    convert push_executes g output false s1 using 1
    simp [s1,s2,Ne.symm hto,Ne.symm hso]
  have h3 := emitEscaped_executes g temp output hto s2
  have h := seq_executes _ _ g h1 (seq_executes _ _ g h2 h3)
  convert h using 1
  · funext i
    by_cases hi : i=output
    · subst i
      simp [s2,s1,hto,Ne.symm hto,Ne.symm hso,pairBits_eq_escaped]
    · by_cases hs : i=source
      · subst i; simp [s2,s1,hso,hst,Ne.symm hst]
      · by_cases hh : i=temp
        · subst i; simp [s2,s1,hi,hs,ht]
        · simp [s2,s1,hi,hs,hh]
  · simp [s2,s1,hto]
    omega

end HiddenCircuits.Approximation.SelfReduction.Runtime
