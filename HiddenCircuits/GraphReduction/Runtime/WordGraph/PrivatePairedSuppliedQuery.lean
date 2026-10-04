import HiddenCircuits.GraphReduction.Runtime.WordGraph.PairedQuery
import HiddenCircuits.GraphReduction.Runtime.CliqueFrontEnumeration
import HiddenCircuits.GraphReduction.Runtime.PrivateSuppliedQuery
import HiddenCircuits.GraphReduction.Runtime.WordGraph.CliquePairedSize

namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.PrivatePairedSuppliedQuery
open Complexity OracleBlock BinaryArithmetic Polynomial
open PairedQuery (state frontEmbedding matrixEmbedding)
set_option maxHeartbeats 900000

def suppliedEmbedding : Fin 64 ↪ Fin 77 := Fin.castAddEmb 13

noncomputable def program : OracleBlock 76 := seq (copyOn 73 56 57 (by decide) (by decide) (by decide))
  (seq (rename (CliqueFront.program true) frontEmbedding)
    (seq (moveOn 56 73 57 (by decide) (by decide) (by decide)) (rename PrivateSuppliedQuery.program suppliedEmbedding)))

theorem program_executes {p : ℕ} (g : BitString → ℕ) (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) :
    ∃c,program.Executes g (state (2*p) ps.length s 0 (stateBits S) (stateBits T) (pairStream ps) [] [])
      (state (2*p) ps.length s (CliqueEmitter.graphInput true (fun i=>ps.get i) S T s).1 (stateBits S) (stateBits T)
        (pairStream ps) (CliqueEmitter.descriptor true (fun i=>ps.get i) S T s) (PrivateSuppliedQuery.bits (fun i=>ps.get i) S T s)) c ∧
      c≤CliqueFront.bound (2*p) ps.length s (CliqueEmitter.descriptor true (fun i=>ps.get i) S T s).length+
        PrivateSuppliedQuery.time.eval ((CliqueEmitter.graphInput true (fun i=>ps.get i) S T s).1+(CliqueEmitter.descriptor true (fun i=>ps.get i) S T s).length)+
        11*(pairStream ps).length+13 := by
  let N := (CliqueEmitter.graphInput true (fun i=>ps.get i) S T s).1
  let D := CliqueEmitter.descriptor true (fun i=>ps.get i) S T s
  let start := state (2*p) ps.length s 0 (stateBits S) (stateBits T) (pairStream ps) [] []
  let a := Function.update start (56:Fin 77) (pairStream ps)
  let b := Function.update (state (2*p) ps.length s N (stateBits S) (stateBits T) [] D []) (56:Fin 77) (pairStream ps)
  let middle := state (2*p) ps.length s N (stateBits S) (stateBits T) (pairStream ps) D []
  have h₁ : (copyOn (73:Fin 77) 56 57 (by decide) (by decide) (by decide)).Executes g start a (5*(pairStream ps).length+2) := by
    simpa [a,start,state] using copyOn_executes g (73:Fin 77) 56 57 (by decide) (by decide) (by decide) start rfl
  obtain ⟨x,hx,hxb⟩ := CliqueFront.program_executes g true ps (stateBits S) (stateBits T) s (by simp) (by simp)
  rw [CliquePairedQuery.descriptor_eq true,CliquePairedQuery.count_eq true] at hx
  rw [CliquePairedQuery.descriptor_eq true] at hxb
  have h₂ : (rename (CliqueFront.program true) frontEmbedding).Executes g a b x := by
    apply rename_executes_to (CliqueFront.program true) frontEmbedding g hx
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
  obtain ⟨y,hy,hyb⟩ := PrivateSuppliedQuery.program_executes g (fun i=>ps.get i) S T s
  change y≤PrivateSuppliedQuery.time.eval ((CliqueEmitter.graphInput true (fun i=>ps.get i) S T s).1+(CliqueEmitter.descriptor true (fun i=>ps.get i) S T s).length) at hyb
  have h₄ : (rename PrivateSuppliedQuery.program suppliedEmbedding).Executes g middle
      (state (2*p) ps.length s N (stateBits S) (stateBits T) (pairStream ps) D (PrivateSuppliedQuery.bits (fun i=>ps.get i) S T s)) y := by
    apply rename_executes_to PrivateSuppliedQuery.program suppliedEmbedding g hy
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · clear hy hyb
      intro i hi
      have h7:i.val≠7 := by intro h;exact hi 7 (Fin.ext h.symm)
      simp only [middle,state,h7,if_false]
  exact ⟨_,seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ h₄)),by omega⟩
noncomputable def time : Polynomial ℕ := 4000*(X+1)^3+PrivateSuppliedQuery.time.comp (390*(X+1)^3)+154*(X+1)^2+13

theorem program_polynomial {p : ℕ} (g : BitString → ℕ) (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) :
    ∃c,program.Executes g (PairedQuery.state (2*p) ps.length s 0 (stateBits S) (stateBits T) (pairStream ps) [] [])
      (PairedQuery.state (2*p) ps.length s (CliqueEmitter.graphInput true (fun i=>ps.get i) S T s).1 (stateBits S) (stateBits T)
        (pairStream ps) (CliqueEmitter.descriptor true (fun i=>ps.get i) S T s) (PrivateSuppliedQuery.bits (fun i=>ps.get i) S T s)) c ∧
      c≤time.eval (p+ps.length+s) := by
  obtain ⟨c,hc,hb⟩ := program_executes g ps S T s
  refine ⟨c,hc,hb.trans ?_⟩
  let M:=p+ps.length+s
  have hp:p≤M:=by dsimp[M];omega
  have hh:ps.length≤M:=by dsimp[M];omega
  have hs:s≤M:=by dsimp[M];omega
  obtain ⟨hn,hd,hw⟩ := CliquePairedQuery.data_size_bounds true ps S T s M hp hh hs
  have hf := CliquePairedQuery.front_bound true ps S T s M hp hh hs
  have hsum : (CliqueEmitter.graphInput true (fun i=>ps.get i) S T s).1+(CliqueEmitter.descriptor true (fun i=>ps.get i) S T s).length≤390*(M+1)^3 := by
    have hpow:(M+1)^2≤(M+1)^3:=by nlinarith [Nat.mul_le_mul_left ((M+1)*(M+1)) (show 1≤M+1 by omega)]
    omega
  have hg := polynomial_nat_eval_mono PrivateSuppliedQuery.time hsum
  simp only [time,eval_add,eval_mul,eval_pow,eval_ofNat,eval_one,eval_X,eval_comp]
  dsimp only [M] at *
  omega
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (rename_queryFree _ _ (CliqueFront.program_queryFree true))
    (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _) (rename_queryFree _ _ PrivateSuppliedQuery.program_queryFree)))
end HiddenCircuits.GraphReduction.Runtime.WordGraph.PrivatePairedSuppliedQuery
