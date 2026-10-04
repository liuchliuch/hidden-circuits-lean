import HiddenCircuits.GraphReduction.Runtime.WordGraph.PairedQuery
import HiddenCircuits.GraphReduction.Runtime.CliqueFrontEnumeration
import HiddenCircuits.GraphReduction.Runtime.CliqueDescriptorSize

namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.CliquePairedQuery
open Complexity OracleBlock BinaryArithmetic
open PairedQuery (state frontEmbedding matrixEmbedding)
set_option maxHeartbeats 900000

noncomputable def program (mode : Bool) : OracleBlock 76 := seq (copyOn 73 56 57 (by decide) (by decide) (by decide))
  (seq (rename (CliqueFront.program mode) frontEmbedding)
    (seq (moveOn 56 73 57 (by decide) (by decide) (by decide)) (rename (CliqueEmitter.program mode) matrixEmbedding)))

lemma descriptor_eq {p : ℕ} (mode : Bool) (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) :
    CliqueFront.descriptor mode ps (stateBits S) (stateBits T) s=CliqueEmitter.descriptor mode (fun i=>ps.get i) S T s := by
  cases mode
  · exact CliqueFront.descriptor_false_eq ps S T s
  · exact CliqueFront.descriptor_true_eq ps S T s
lemma count_eq {p : ℕ} (mode : Bool) (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) :
    (CliqueFront.records mode ps (stateBits S) (stateBits T) s).length=(CliqueEmitter.graphInput mode (fun i=>ps.get i) S T s).1 := by
  cases mode
  · rw [←CliqueFront.unitRecords_eq,unitRecords_length];rfl
  · rw [←CliqueFront.privateRecords_eq,privateRecords_length];rfl

theorem program_executes {p : ℕ} (g : BitString → ℕ) (mode : Bool) (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) :
    ∃c,(program mode).Executes g (state (2*p) ps.length s 0 (stateBits S) (stateBits T) (pairStream ps) [] [])
      (state (2*p) ps.length s (CliqueEmitter.graphInput mode (fun i=>ps.get i) S T s).1 (stateBits S) (stateBits T)
        (pairStream ps) (CliqueEmitter.descriptor mode (fun i=>ps.get i) S T s) (CliqueEmitter.graphInput mode (fun i=>ps.get i) S T s).encode) c ∧
      c≤CliqueFront.bound (2*p) ps.length s (CliqueEmitter.descriptor mode (fun i=>ps.get i) S T s).length+
        CliqueEmitter.time.eval ((CliqueEmitter.graphInput mode (fun i=>ps.get i) S T s).1+(CliqueEmitter.descriptor mode (fun i=>ps.get i) S T s).length)+
        11*(pairStream ps).length+13 := by
  let N := (CliqueEmitter.graphInput mode (fun i=>ps.get i) S T s).1
  let D := CliqueEmitter.descriptor mode (fun i=>ps.get i) S T s
  let start := state (2*p) ps.length s 0 (stateBits S) (stateBits T) (pairStream ps) [] []
  let a := Function.update start (56:Fin 77) (pairStream ps)
  let b := Function.update (state (2*p) ps.length s N (stateBits S) (stateBits T) [] D []) (56:Fin 77) (pairStream ps)
  let middle := state (2*p) ps.length s N (stateBits S) (stateBits T) (pairStream ps) D []
  have h₁ : (copyOn (73:Fin 77) 56 57 (by decide) (by decide) (by decide)).Executes g start a (5*(pairStream ps).length+2) := by
    simpa [a,start,state] using copyOn_executes g (73:Fin 77) 56 57 (by decide) (by decide) (by decide) start rfl
  obtain ⟨x,hx,hxb⟩ := CliqueFront.program_executes g mode ps (stateBits S) (stateBits T) s (by simp) (by simp)
  rw [descriptor_eq mode,count_eq mode] at hx
  rw [descriptor_eq mode] at hxb
  have h₂ : (rename (CliqueFront.program mode) frontEmbedding).Executes g a b x := by
    apply rename_executes_to (CliqueFront.program mode) frontEmbedding g hx
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · clear hx hxb
      intro i hi
      have h0:i.val≠0 := by intro h;exact hi 5 (Fin.ext h.symm)
      have h8:i.val≠8 := by intro h;exact hi 18 (Fin.ext h.symm)
      have h73:i.val≠73 := by intro h;exact hi 16 (Fin.ext h.symm)
      by_cases h56:i=56
      · subst i;rfl
      · simp only [a,b,start,Function.update_of_ne h56,state,h0,h8,h73,if_false]
  have h₃ : (moveOn (56:Fin 77) 73 57 (by decide) (by decide) (by decide)).Executes g b middle (6*(pairStream ps).length+5) := by
    convert moveOn_executes g (56:Fin 77) 73 57 (by decide) (by decide) (by decide) b rfl using 1
    funext i
    by_cases h56:i=56
    · subst i;rfl
    · by_cases h73:i=73
      · subst i
        change pairStream ps=pairStream ps++[]
        simp only [List.append_nil]
      · simp only [b,middle,Function.update_of_ne h56,Function.update_of_ne h73]
        have hn:i.val≠73:=by intro h;exact h73 (Fin.ext h)
        simp only [state,hn,if_false]
  obtain ⟨y,hy,hyb⟩ := CliqueEmitter.program_polynomial g mode (fun i=>ps.get i) S T s
  have h₄ : (rename (CliqueEmitter.program mode) matrixEmbedding).Executes g middle
      (state (2*p) ps.length s N (stateBits S) (stateBits T) (pairStream ps) D (CliqueEmitter.graphInput mode (fun i=>ps.get i) S T s).encode) y := by
    apply rename_executes_to (CliqueEmitter.program mode) matrixEmbedding g hy
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · clear hy hyb
      intro i hi
      have h7:i.val≠7 := by intro h;exact hi 7 (Fin.ext h.symm)
      simp only [middle,state,h7,if_false]
  exact ⟨_,seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ h₄)),by omega⟩
end HiddenCircuits.GraphReduction.Runtime.WordGraph.CliquePairedQuery
