import HiddenCircuits.GraphReduction.Runtime.MonotoneDescriptor
import HiddenCircuits.GraphReduction.Runtime.ListLookup

/-! A literal parser for structural query vertex records. -/
namespace HiddenCircuits.GraphReduction.Runtime
open Complexity Complexity.OracleBlock

noncomputable def readBit {k : ℕ} (source output : Fin (k+1)) : OracleBlock k :=
  branchPop source (push output false) (push output false) (push output true)

theorem readBit_executes {k : ℕ} (g : BitString → ℕ) (source output : Fin (k+1))
    (hne : source≠output) (s : Store k) (b : Bool) (rest : BitString)
    (hs : s source=b::rest) (ho : s output=[]) :
    (readBit source output).Executes g s
      (Function.update (Function.update s source rest) output [b]) 3 := by
  have hp : (push output b).Executes g (Function.update s source rest)
      (Function.update (Function.update s source rest) output [b]) 1 := by
    simpa only [Function.update_of_ne hne.symm,ho] using
      push_executes g output b (Function.update s source rest)
  cases b
  · exact branchPop_false _ _ _ _ g hs hp
  · exact branchPop_true _ _ _ _ g hs hp
lemma readBit_queryFree {k : ℕ} (source output : Fin (k+1)) : (readBit source output).QueryFree :=
  branchPop_queryFree _ _ _ _ (push_queryFree _ _) (push_queryFree _ _) (push_queryFree _ _)

def recordFields (v : VertexRecord) : Fin 9 → BitString :=
  ![[v.side],[v.probe],[v.cut.leftRise],[v.cut.leftDrop],[v.cut.rightRise],[v.cut.rightDrop],
    List.replicate v.layer true,List.replicate v.track true,List.replicate v.cut.index true]
def recordParseStore (source : BitString) (fields : Fin 9 → BitString) (tmp flag : BitString) : Store 11 :=
  ![source,fields 0,fields 1,fields 2,fields 3,fields 4,fields 5,fields 6,fields 7,fields 8,tmp,flag]
def recordPrefix (v : VertexRecord) : BitString :=
  [v.side,v.probe,v.cut.leftRise,v.cut.leftDrop,v.cut.rightRise,v.cut.rightDrop]
def recordTail (v : VertexRecord) : BitString :=
  pairBits (List.replicate v.layer true) (pairBits (List.replicate v.track true) (List.replicate v.cut.index true))
def prefixFields (v : VertexRecord) (j : ℕ) : Fin 9 → BitString :=
  fun i => if i.val<j then recordFields v i else []
def prefixState (v : VertexRecord) (j : ℕ) : Store 11 :=
  recordParseStore ((recordPrefix v).drop j++recordTail v) (prefixFields v j) [] []

noncomputable def recordPrefixParse : OracleBlock 11 := seq (readBit 0 1) (seq (readBit 0 2) (seq (readBit 0 3) (seq (readBit 0 4) (seq (readBit 0 5) (readBit 0 6)))))

theorem recordPrefixParse_executes (g : BitString → ℕ) (v : VertexRecord) :
    recordPrefixParse.Executes g (prefixState v 0) (prefixState v 6) 28 := by
  have h1 : (readBit (0 : Fin 12) 1).Executes g (prefixState v 0) (prefixState v 1) 3 := by
    have h := readBit_executes g (0 : Fin 12) 1 (by decide) (prefixState v 0) v.side
      ((recordPrefix v).drop 1++recordTail v) rfl rfl
    convert h using 1
    funext i; fin_cases i <;> simp [prefixState,prefixFields,recordParseStore,recordFields,recordPrefix]
  have h2 : (readBit (0 : Fin 12) 2).Executes g (prefixState v 1) (prefixState v 2) 3 := by
    have h := readBit_executes g (0 : Fin 12) 2 (by decide) (prefixState v 1) v.probe
      ((recordPrefix v).drop 2++recordTail v) rfl rfl
    convert h using 1
    funext i; fin_cases i <;> simp [prefixState,prefixFields,recordParseStore,recordFields,recordPrefix]
  have h3 : (readBit (0 : Fin 12) 3).Executes g (prefixState v 2) (prefixState v 3) 3 := by
    have h := readBit_executes g (0 : Fin 12) 3 (by decide) (prefixState v 2) v.cut.leftRise
      ((recordPrefix v).drop 3++recordTail v) rfl rfl
    convert h using 1
    funext i; fin_cases i <;> simp [prefixState,prefixFields,recordParseStore,recordFields,recordPrefix]
  have h4 : (readBit (0 : Fin 12) 4).Executes g (prefixState v 3) (prefixState v 4) 3 := by
    have h := readBit_executes g (0 : Fin 12) 4 (by decide) (prefixState v 3) v.cut.leftDrop
      ((recordPrefix v).drop 4++recordTail v) rfl rfl
    convert h using 1
    funext i; fin_cases i <;> simp [prefixState,prefixFields,recordParseStore,recordFields,recordPrefix]
  have h5 : (readBit (0 : Fin 12) 5).Executes g (prefixState v 4) (prefixState v 5) 3 := by
    have h := readBit_executes g (0 : Fin 12) 5 (by decide) (prefixState v 4) v.cut.rightRise
      ((recordPrefix v).drop 5++recordTail v) rfl rfl
    convert h using 1
    funext i; fin_cases i <;> simp [prefixState,prefixFields,recordParseStore,recordFields,recordPrefix]
  have h6 : (readBit (0 : Fin 12) 6).Executes g (prefixState v 5) (prefixState v 6) 3 := by
    have h := readBit_executes g (0 : Fin 12) 6 (by decide) (prefixState v 5) v.cut.rightDrop
      ((recordPrefix v).drop 6++recordTail v) rfl rfl
    convert h using 1
    funext i; fin_cases i <;> simp [prefixState,prefixFields,recordParseStore,recordFields,recordPrefix]
  exact seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 (seq_executes _ _ g h4 (seq_executes _ _ g h5 (h6)))))


end HiddenCircuits.GraphReduction.Runtime
