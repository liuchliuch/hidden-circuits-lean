import HiddenCircuits.GraphReduction.Runtime.WordGraph.PairedQuery
import HiddenCircuits.GraphReduction.Runtime.DescriptorFrontEnumeration
import HiddenCircuits.GraphReduction.Runtime.DescriptorFrontNoQuery
import HiddenCircuits.GraphReduction.Runtime.WordGraph.MonotonePermutationQuery
import HiddenCircuits.GraphReduction.Runtime.WordGraph.PairedSize

namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.MonotonePermutationPairedQuery
open Complexity OracleBlock BinaryArithmetic Polynomial
open WordGraph
def state (width height samples count : ℕ) (source target pairs descriptor output : BitString) : Store 89 := fun i=>
  if hi:i.val<77 then PairedQuery.state width height samples count source target pairs descriptor output ⟨i.val,hi⟩ else []
def frontEmbedding : Fin 20 ↪ Fin 90 := PairedQuery.frontEmbedding.trans (Fin.castAddEmb 13)
set_option maxHeartbeats 900000

def suppliedEmbedding : Fin 64 ↪ Fin 90 where
  toFun i:=if hi:i.val<57 then ⟨i.val,by omega⟩ else ⟨20+i.val,by omega⟩
  inj':=by decide +kernel

noncomputable def program : OracleBlock 89 := seq (copyOn 73 56 57 (by decide) (by decide) (by decide))
  (seq (rename DescriptorFront.program frontEmbedding)
    (seq (moveOn 56 73 57 (by decide) (by decide) (by decide)) (rename MonotonePermutationQuery.program suppliedEmbedding)))

theorem program_executes {p : ℕ} (g : BitString → ℕ) (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) :
    ∃c,program.Executes g (state (2*p) ps.length s 0 (stateBits S) (stateBits T) (pairStream ps) [] [])
      (state (2*p) ps.length s (monotoneGraphInput (fun i=>ps.get i) S T s).1 (stateBits S) (stateBits T)
        (pairStream ps) (monotoneDescriptor (fun i=>ps.get i) S T s) (MonotonePermutationQuery.bits (fun i=>ps.get i) S T s)) c ∧
      c≤DescriptorFront.bound (2*p) ps.length s (monotoneDescriptor (fun i=>ps.get i) S T s).length+
        MonotonePermutationQuery.time.eval ((monotoneGraphInput (fun i=>ps.get i) S T s).1+(monotoneDescriptor (fun i=>ps.get i) S T s).length)+
        11*(pairStream ps).length+13 := by
  let N := (monotoneGraphInput (fun i=>ps.get i) S T s).1
  let D := monotoneDescriptor (fun i=>ps.get i) S T s
  let start := state (2*p) ps.length s 0 (stateBits S) (stateBits T) (pairStream ps) [] []
  let a := Function.update start (56:Fin 90) (pairStream ps)
  let b := Function.update (state (2*p) ps.length s N (stateBits S) (stateBits T) [] D []) (56:Fin 90) (pairStream ps)
  let middle := state (2*p) ps.length s N (stateBits S) (stateBits T) (pairStream ps) D []
  have h₁ : (copyOn (73:Fin 90) 56 57 (by decide) (by decide) (by decide)).Executes g start a (5*(pairStream ps).length+2) := by
    simpa [a,start,state,PairedQuery.state] using copyOn_executes g (73:Fin 90) 56 57 (by decide) (by decide) (by decide) start rfl
  obtain ⟨x,hx,hxb⟩ := DescriptorFront.program_executes g ps (stateBits S) (stateBits T) s (by simp) (by simp)
  rw [DescriptorFront.descriptor_eq,DescriptorFront.count_eq] at hx
  rw [DescriptorFront.descriptor_eq] at hxb
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
      · simp only [a,b,start,Function.update_of_ne h56,state,PairedQuery.state,h0,h8,h73,if_false]
  have h₃ : (moveOn (56:Fin 90) 73 57 (by decide) (by decide) (by decide)).Executes g b middle (6*(pairStream ps).length+5) := by
    convert moveOn_executes g (56:Fin 90) 73 57 (by decide) (by decide) (by decide) b rfl using 1
    funext i
    by_cases h56:i=56
    · subst i;rfl
    · by_cases h73:i=73
      · subst i
        change pairStream ps=pairStream ps++[]
        simp only [List.append_nil]
      · simp only [b,middle,Function.update_of_ne h56,Function.update_of_ne h73]
        have hn:i.val≠73:=by intro h;exact h73 (Fin.ext h)
        simp only [state,PairedQuery.state,hn,if_false]
  obtain ⟨y,hy,hyb⟩ := MonotonePermutationQuery.program_executes g (fun i=>ps.get i) S T s
  change y≤MonotonePermutationQuery.time.eval ((monotoneGraphInput (fun i=>ps.get i) S T s).1+(monotoneDescriptor (fun i=>ps.get i) S T s).length) at hyb
  have h₄ : (rename MonotonePermutationQuery.program suppliedEmbedding).Executes g middle
      (state (2*p) ps.length s N (stateBits S) (stateBits T) (pairStream ps) D (MonotonePermutationQuery.bits (fun i=>ps.get i) S T s)) y := by
    apply rename_executes_to MonotonePermutationQuery.program suppliedEmbedding g hy
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · clear hy hyb
      intro i hi
      have h7:i.val≠7 := by intro h;exact hi 7 (Fin.ext h.symm)
      simp only [middle,state,PairedQuery.state,h7,if_false]
  exact ⟨_,seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ h₄)),by omega⟩
noncomputable def timePolynomial : Polynomial ℕ := 4000*(X+1)^3+MonotonePermutationQuery.time.comp (390*(X+1)^3)+154*(X+1)^2+13

theorem program_polynomial {p : ℕ} (g : BitString → ℕ) (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) :
    ∃c,program.Executes g (state (2*p) ps.length s 0 (stateBits S) (stateBits T) (pairStream ps) [] [])
      (state (2*p) ps.length s (monotoneGraphInput (fun i=>ps.get i) S T s).1 (stateBits S) (stateBits T)
        (pairStream ps) (monotoneDescriptor (fun i=>ps.get i) S T s) (MonotonePermutationQuery.bits (fun i=>ps.get i) S T s)) c ∧
      c≤timePolynomial.eval (p+ps.length+s) := by
  obtain ⟨c,hc,hb⟩ := program_executes g ps S T s
  refine ⟨c,hc,hb.trans ?_⟩
  let M:=p+ps.length+s
  have hp:p≤M:=by dsimp[M];omega
  have hh:ps.length≤M:=by dsimp[M];omega
  have hs:s≤M:=by dsimp[M];omega
  obtain ⟨hn,hd,hw⟩ := PairedQuery.data_size_bounds ps S T s M hp hh hs
  have hf := WordQuery.descriptor_bound ps S T s M hp hh hs
  have hsum : (monotoneGraphInput (fun i=>ps.get i) S T s).1+(monotoneDescriptor (fun i=>ps.get i) S T s).length≤390*(M+1)^3 := by
    have hpow:(M+1)^2≤(M+1)^3:=by nlinarith [Nat.mul_le_mul_left ((M+1)*(M+1)) (show 1≤M+1 by omega)]
    omega
  have hg := polynomial_nat_eval_mono MonotonePermutationQuery.time hsum
  simp only [timePolynomial,eval_add,eval_mul,eval_pow,eval_ofNat,eval_one,eval_X,eval_comp]
  dsimp only [M] at *
  omega
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (rename_queryFree _ _ (DescriptorFront.program_queryFree))
    (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _) (rename_queryFree _ _ MonotonePermutationQuery.program_queryFree)))
end HiddenCircuits.GraphReduction.Runtime.WordGraph.MonotonePermutationPairedQuery
