import HiddenCircuits.GraphReduction.Runtime.WordGraph.CliquePairedQuery
import HiddenCircuits.GraphReduction.Runtime.WordGraph.PairedSize

namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.CliquePairedQuery
open Complexity OracleBlock BinaryArithmetic Polynomial

lemma count_size {p : ℕ} (mode : Bool) (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) :
    (CliqueEmitter.graphInput mode (fun i=>ps.get i) S T s).1≤(2*p+s)*(2*ps.length+1) := by
  rw [←count_eq,CliqueFront.records]
  simp only [List.length_append,DescriptorRectangle.records_length,DescriptorOdd.records_length]
  have h := even_records_size (2*p) ps.length (stateBits S) (stateBits T) (by simp) (by simp)
  have ht : (CliqueFront.tailRecords mode s ps.length).length≤s*ps.length := by
    cases mode <;> simp [CliqueFront.tailRecords,DescriptorRectangle.records_length]
  nlinarith

lemma data_size_bounds {p : ℕ} (mode : Bool) (ps : List (CutPair p)) (S T : State (2*p) p) (s M : ℕ)
    (hp:p≤M) (hh:ps.length≤M) (hs:s≤M) :
    (CliqueEmitter.graphInput mode (fun i=>ps.get i) S T s).1≤10*(M+1)^2 ∧
    (CliqueEmitter.descriptor mode (fun i=>ps.get i) S T s).length≤380*(M+1)^3 ∧
    (pairStream ps).length≤14*(M+1)^2 := by
  have hn : (CliqueEmitter.graphInput mode (fun i=>ps.get i) S T s).1≤10*(M+1)^2 := by
    calc
      _≤(2*p+s)*(2*ps.length+1) := count_size mode ps S T s
      _≤(2*M+M)*(2*M+1) := by gcongr
      _≤10*(M+1)^2 := by ring_nf;omega
  refine ⟨hn,?_,?_⟩
  · calc
      _≤(CliqueEmitter.graphInput mode (fun i=>ps.get i) S T s).1*(18+4*ps.length+12*p+4*s) := CliqueEmitter.descriptor_size _ _ _ _ _
      _≤(10*(M+1)^2)*(18+4*M+12*M+4*M) := by gcongr
      _≤380*(M+1)^3 := by ring_nf;omega
  · calc
      _≤ps.length*(10+4*p) := pairStream_length_bound ps
      _≤M*(10+4*M) := by gcongr
      _≤14*(M+1)^2 := by ring_nf;omega

lemma front_bound {p : ℕ} (mode : Bool) (ps : List (CutPair p)) (S T : State (2*p) p) (s M : ℕ)
    (hp:p≤M) (hh:ps.length≤M) (hs:s≤M) :
    CliqueFront.bound (2*p) ps.length s (CliqueEmitter.descriptor mode (fun i=>ps.get i) S T s).length≤4000*(M+1)^3 := by
  have hd := (data_size_bounds mode ps S T s M hp hh hs).2.1
  unfold CliqueFront.bound DescriptorEven.bound CliqueFront.probeBound
  calc
    _≤(M+2)*((2*M)*(20*M+20*(2*M)+140)+20)+M+20+5*M+6+
      (M*((2*M)*(20*M+34*(2*M)+125)+8*(2*M)+128)+4)+
      ((M+1)*(M*(20*(M+1)+20*M+125)+19)+68)+(M*(M*(20*M+20*M+125)+19)+68)+2*(380*(M+1)^3)+47 := by gcongr
    _≤4000*(M+1)^3 := by ring_nf;omega

noncomputable def time : Polynomial ℕ := 4000*(X+1)^3+CliqueEmitter.time.comp (390*(X+1)^3)+154*(X+1)^2+13

theorem program_polynomial {p : ℕ} (g : BitString → ℕ) (mode : Bool) (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) :
    ∃c,(program mode).Executes g (PairedQuery.state (2*p) ps.length s 0 (stateBits S) (stateBits T) (pairStream ps) [] [])
      (PairedQuery.state (2*p) ps.length s (CliqueEmitter.graphInput mode (fun i=>ps.get i) S T s).1 (stateBits S) (stateBits T)
        (pairStream ps) (CliqueEmitter.descriptor mode (fun i=>ps.get i) S T s) (CliqueEmitter.graphInput mode (fun i=>ps.get i) S T s).encode) c ∧
      c≤time.eval (p+ps.length+s) := by
  obtain ⟨c,hc,hb⟩ := program_executes g mode ps S T s
  refine ⟨c,hc,hb.trans ?_⟩
  let M:=p+ps.length+s
  have hp:p≤M:=by dsimp[M];omega
  have hh:ps.length≤M:=by dsimp[M];omega
  have hs:s≤M:=by dsimp[M];omega
  obtain ⟨hn,hd,hw⟩ := data_size_bounds mode ps S T s M hp hh hs
  have hf := front_bound mode ps S T s M hp hh hs
  have hsum : (CliqueEmitter.graphInput mode (fun i=>ps.get i) S T s).1+(CliqueEmitter.descriptor mode (fun i=>ps.get i) S T s).length≤390*(M+1)^3 := by
    have hpow:(M+1)^2≤(M+1)^3:=by nlinarith [Nat.mul_le_mul_left ((M+1)*(M+1)) (show 1≤M+1 by omega)]
    omega
  have hg := polynomial_nat_eval_mono CliqueEmitter.time hsum
  simp only [time,eval_add,eval_mul,eval_pow,eval_ofNat,eval_one,eval_X,eval_comp]
  dsimp only [M] at *
  omega
lemma program_queryFree (mode : Bool) : (program mode).QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (rename_queryFree _ _ (CliqueFront.program_queryFree mode))
    (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _) (rename_queryFree _ _ (CliqueEmitter.program_queryFree mode))))
end HiddenCircuits.GraphReduction.Runtime.WordGraph.CliquePairedQuery
