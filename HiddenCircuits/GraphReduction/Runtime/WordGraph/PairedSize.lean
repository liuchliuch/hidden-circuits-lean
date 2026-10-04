import HiddenCircuits.GraphReduction.Runtime.WordGraph.PairedQuery
import HiddenCircuits.Complexity.PolynomialBounds

namespace HiddenCircuits.GraphReduction.Runtime.WordGraph
open Complexity OracleBlock BinaryArithmetic Polynomial

lemma even_records_size (width height : ℕ) (S T : BitString) (hS : S.length=width) (hT : T.length=width) :
    (DescriptorEven.records width height S T).length≤width*(height+1) := by
  cases height with
  | zero =>
    have h := DescriptorMaskRow.records_length_le (DescriptorEven.vertex 0) (DescriptorMaskDifference.difference S T)
    rw [DescriptorMaskDifference.difference_length S T (hS.trans hT.symm),hS] at h
    simpa only [DescriptorEven.records,Nat.zero_add,Nat.mul_one] using h
  | succ n =>
    have ha := DescriptorMaskRow.records_length_le (DescriptorEven.vertex 0) S
    have hb := DescriptorMaskRow.records_length_le (DescriptorEven.vertex (n+1)) (DescriptorMaskDifference.difference (List.replicate width true) T)
    rw [DescriptorMaskDifference.difference_length _ T (by simp [hT]),List.length_replicate] at hb
    rw [hS] at ha
    simp only [DescriptorEven.records,List.length_append,DescriptorRectangle.records_length]
    nlinarith

namespace PairedQuery
lemma count_size {p : ℕ} (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) :
    (monotoneGraphInput (fun i=>ps.get i) S T s).1≤(2*p)*(2*ps.length+1)+2*s*ps.length := by
  rw [←count_eq,DescriptorFront.records]
  simp only [List.length_append,DescriptorRectangle.records_length,DescriptorOdd.records_length]
  have h := even_records_size (2*p) ps.length (stateBits S) (stateBits T) (by simp) (by simp)
  nlinarith

lemma data_size_bounds {p : ℕ} (ps : List (CutPair p)) (S T : State (2*p) p) (s M : ℕ)
    (hp : p≤M) (hh : ps.length≤M) (hs : s≤M) :
    (monotoneGraphInput (fun i=>ps.get i) S T s).1≤10*(M+1)^2 ∧
    (monotoneDescriptor (fun i=>ps.get i) S T s).length≤380*(M+1)^3 ∧
    (pairStream ps).length≤14*(M+1)^2 := by
  have hn : (monotoneGraphInput (fun i=>ps.get i) S T s).1≤10*(M+1)^2 := by
    calc
      _≤(2*p)*(2*ps.length+1)+2*s*ps.length := count_size ps S T s
      _≤(2*M)*(2*M+1)+2*M*M := by gcongr
      _≤10*(M+1)^2 := by ring_nf;omega
  refine ⟨hn,?_,?_⟩
  · calc
      _≤(monotoneGraphInput (fun i=>ps.get i) S T s).1*(18+4*ps.length+12*p+4*s) := monotoneDescriptor_size _ _ _ _
      _≤(10*(M+1)^2)*(18+4*M+12*M+4*M) := by gcongr
      _≤380*(M+1)^3 := by ring_nf;omega
  · calc
      _≤ps.length*(10+4*p) := pairStream_length_bound ps
      _≤M*(10+4*M) := by gcongr
      _≤14*(M+1)^2 := by ring_nf;omega
end PairedQuery

namespace WordQuery
lemma descriptor_bound {p : ℕ} (ps : List (CutPair p)) (S T : State (2*p) p) (s M : ℕ)
    (hp : p≤M) (hh : ps.length≤M) (hs : s≤M) :
    DescriptorFront.bound (2*p) ps.length s (monotoneDescriptor (fun i=>ps.get i) S T s).length≤4000*(M+1)^3 := by
  have hd := (PairedQuery.data_size_bounds ps S T s M hp hh hs).2.1
  unfold DescriptorFront.bound DescriptorEven.bound
  calc
    _≤(M+2)*((2*M)*(20*M+20*(2*M)+140)+20)+M+20+5*M+6+
      2*(M*(M*(20*M+20*M+125)+19)+68)+
      (M*((2*M)*(20*M+34*(2*M)+125)+8*(2*M)+128)+4)+2*(380*(M+1)^3)+39 := by gcongr
    _≤4000*(M+1)^3 := by ring_nf;omega
end WordQuery

namespace PairedQuery
noncomputable def time : Polynomial ℕ := 4000*(X+1)^3+graphQueryTime.comp (390*(X+1)^3)+154*(X+1)^2+13

theorem program_polynomial {p : ℕ} (g : BitString → ℕ) (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) :
    ∃c,program.Executes g (state (2*p) ps.length s 0 (stateBits S) (stateBits T) (pairStream ps) [] [])
      (state (2*p) ps.length s (monotoneGraphInput (fun i=>ps.get i) S T s).1 (stateBits S) (stateBits T)
        (pairStream ps) (monotoneDescriptor (fun i=>ps.get i) S T s) (monotoneGraphInput (fun i=>ps.get i) S T s).encode) c ∧
      c≤time.eval (p+ps.length+s) := by
  obtain ⟨c,hc,hb⟩ := program_executes g ps S T s
  refine ⟨c,hc,hb.trans ?_⟩
  let M := p+ps.length+s
  have hp:p≤M:=by dsimp[M];omega
  have hh:ps.length≤M:=by dsimp[M];omega
  have hs:s≤M:=by dsimp[M];omega
  obtain ⟨hn,hd,hw⟩ := data_size_bounds ps S T s M hp hh hs
  have hf := WordQuery.descriptor_bound ps S T s M hp hh hs
  have hsum : (monotoneGraphInput (fun i=>ps.get i) S T s).1+(monotoneDescriptor (fun i=>ps.get i) S T s).length≤390*(M+1)^3 := by
    have hpow : (M+1)^2≤(M+1)^3 := by nlinarith [Nat.mul_le_mul_left ((M+1)*(M+1)) (show 1≤M+1 by omega)]
    omega
  have hg := polynomial_nat_eval_mono graphQueryTime hsum
  simp only [time,eval_add,eval_mul,eval_pow,eval_ofNat,eval_one,eval_X,eval_comp]
  dsimp only [M] at *
  omega
end PairedQuery
end HiddenCircuits.GraphReduction.Runtime.WordGraph
