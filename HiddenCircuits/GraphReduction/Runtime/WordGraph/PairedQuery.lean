import HiddenCircuits.GraphReduction.Runtime.DescriptorFrontEnumeration
import HiddenCircuits.GraphReduction.Runtime.MonotoneEmitter
import HiddenCircuits.Complexity.OracleMove

namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.PairedQuery
open Complexity OracleBlock BinaryArithmetic
set_option maxHeartbeats 900000

def state (width height samples count : ℕ) (source target pairs descriptor output : BitString) : Store 76 := fun i =>
  if i.val=0 then List.replicate count true else if i.val=7 then output else if i.val=8 then descriptor
  else if i.val=65 then List.replicate width true else if i.val=67 then List.replicate height true
  else if i.val=69 then source else if i.val=70 then target else if i.val=73 then pairs
  else if i.val=74 then List.replicate samples true else []

def frontEmbedding : Fin 20 ↪ Fin 77 where
  toFun i := if i.val=5 then 0 else if i.val=18 then 8 else ⟨i.val+57,by omega⟩
  inj' := by decide +kernel

def matrixEmbedding : Fin 57 ↪ Fin 77 := Fin.castAddEmb 20
noncomputable def program : OracleBlock 76 := seq (copyOn 73 56 57 (by decide) (by decide) (by decide))
  (seq (rename DescriptorFront.program frontEmbedding)
    (seq (moveOn 56 73 57 (by decide) (by decide) (by decide)) (rename monotoneEmitter matrixEmbedding)))

lemma descriptor_eq {p : ℕ} (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) :
    DescriptorFront.descriptor ps (stateBits S) (stateBits T) s=monotoneDescriptor (fun i=>ps.get i) S T s := DescriptorFront.descriptor_eq ps S T s
lemma count_eq {p : ℕ} (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) :
    (DescriptorFront.records ps (stateBits S) (stateBits T) s).length=(monotoneGraphInput (fun i=>ps.get i) S T s).1 := DescriptorFront.count_eq ps S T s

theorem program_executes {p : ℕ} (g : BitString → ℕ) (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) :
    ∃c,program.Executes g (state (2*p) ps.length s 0 (stateBits S) (stateBits T) (pairStream ps) [] [])
      (state (2*p) ps.length s (monotoneGraphInput (fun i=>ps.get i) S T s).1 (stateBits S) (stateBits T)
        (pairStream ps) (monotoneDescriptor (fun i=>ps.get i) S T s) (monotoneGraphInput (fun i=>ps.get i) S T s).encode) c ∧
      c≤DescriptorFront.bound (2*p) ps.length s (monotoneDescriptor (fun i=>ps.get i) S T s).length+
        graphQueryTime.eval ((monotoneGraphInput (fun i=>ps.get i) S T s).1+(monotoneDescriptor (fun i=>ps.get i) S T s).length)+
        11*(pairStream ps).length+13 := by
  let N := (monotoneGraphInput (fun i=>ps.get i) S T s).1
  let D := monotoneDescriptor (fun i=>ps.get i) S T s
  let start := state (2*p) ps.length s 0 (stateBits S) (stateBits T) (pairStream ps) [] []
  let a := Function.update start (56:Fin 77) (pairStream ps)
  let b := Function.update (state (2*p) ps.length s N (stateBits S) (stateBits T) [] D []) (56:Fin 77) (pairStream ps)
  let middle := state (2*p) ps.length s N (stateBits S) (stateBits T) (pairStream ps) D []
  have h₁ : (copyOn (73:Fin 77) 56 57 (by decide) (by decide) (by decide)).Executes g start a (5*(pairStream ps).length+2) := by
    simpa [a,start,state] using copyOn_executes g (73:Fin 77) 56 57 (by decide) (by decide) (by decide) start rfl
  obtain ⟨x,hx,hxb⟩ := DescriptorFront.program_executes g ps (stateBits S) (stateBits T) s (by simp) (by simp)
  rw [descriptor_eq,count_eq] at hx
  rw [descriptor_eq] at hxb
  have h₂ : (rename DescriptorFront.program frontEmbedding).Executes g a b x := by
    apply rename_executes_to DescriptorFront.program frontEmbedding g hx
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
  obtain ⟨y,hy,hyb⟩ := monotoneEmitter_polynomial (fun i=>ps.get i) S T s g
  have h₄ : (rename monotoneEmitter matrixEmbedding).Executes g middle
      (state (2*p) ps.length s N (stateBits S) (stateBits T) (pairStream ps) D (monotoneGraphInput (fun i=>ps.get i) S T s).encode) y := by
    apply rename_executes_to monotoneEmitter matrixEmbedding g hy
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · clear hy hyb
      intro i hi
      have h7:i.val≠7 := by intro h;exact hi 7 (Fin.ext h.symm)
      simp only [middle,state,h7,if_false]
  exact ⟨_,seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ h₄)),by omega⟩
end HiddenCircuits.GraphReduction.Runtime.WordGraph.PairedQuery
