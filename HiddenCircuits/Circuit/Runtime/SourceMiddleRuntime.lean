import HiddenCircuits.Circuit.Runtime.SourceRowPorts
import HiddenCircuits.Circuit.Runtime.SourceFoldBounds

/-! Actual second-spectral iteration over complete geometric
rows, preserving one global rational prefix bound and cleaning both clocks. -/
namespace HiddenCircuits.Circuit.Runtime.SourceMiddle
open HiddenCircuits.Complexity OracleBlock BinaryArithmetic Polynomial SourceQueryRecovery
open HiddenCircuits.DH.Runtime

def count {n : ℕ} (w : List (ConstraintGate n)) : ℕ := Fintype.card (SpectralIndex (signOccurrences w))
lemma count_positive {n : ℕ} (w : List (ConstraintGate n)) : 0<count w := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨⟨0,by omega⟩,⟨0,by omega⟩⟩⟩
def dataState {k n : ℕ} (w : List (ConstraintGate n)) (a r s : ℕ) (acc : RationalAccumulator.Ratio) : Store (k+66) :=
  FramedFor.frame (SourceRow.state (k:=k) w a r s acc) (List.replicate (count w-1) true)
def state {k n : ℕ} (w : List (ConstraintGate n)) (a r s : ℕ) (acc : RationalAccumulator.Ratio) : Store (k+67) :=
  FramedFor.frame (dataState (k:=k) w a r s acc) []
def parameterPort (k : ℕ) (i : Fin 64) : Fin (k+67) := FramedFor.embedding (k+65) (SourceRow.parameterPort k i)
noncomputable def body {k : ℕ} (W : OracleBlock k) : OracleBlock (k+66) := rename (SourceRow.program W) (FramedFor.embedding (k+65))
noncomputable def program {k : ℕ} (W : OracleBlock k) : OracleBlock (k+67) :=
  FramedFor.program (Fin.last (k+66)) (parameterPort k 3) (parameterPort k 24)
    (Ne.symm (FramedFor.body_ne_clock (SourceRow.parameterPort k 24))) (body W)
noncomputable def result {n : ℕ} (hn : 0<n) (a : ℕ) (w : List (ConstraintGate n)) (r : FirstIndex w) (acc : RationalAccumulator.Ratio) : RationalAccumulator.Ratio :=
  RationalAccumulator.run acc (SourceSampleIntegers.middleItems hn a w r)
noncomputable def time (p : Polynomial ℕ) : Polynomial ℕ := (X+1)^2*(SourceRow.time p+5)+6*(X+1)^2+12

lemma parameter_value {k n : ℕ} (w : List (ConstraintGate n)) (a r s : ℕ) (acc : RationalAccumulator.Ratio) (i : Fin 64) :
    dataState (k:=k) w a r s acc (parameterPort k i)=SourceSample.store (SourceSample.canonical w a r s 0) {accumulator:=acc} i := by
  simp [dataState,parameterPort,SourceRow.parameter_value]
lemma update_index {k n : ℕ} (w : List (ConstraintGate n)) (a r s s' : ℕ) (acc : RationalAccumulator.Ratio) :
    Function.update (dataState (k:=k) w a r s acc) (parameterPort k 3) (List.replicate s' true)=dataState w a r s' acc := by
  unfold dataState parameterPort
  rw [FramedFor.update_body,SourceRow.update_s]

set_option maxHeartbeats 1200000 in
theorem program_executes {k : ℕ} (W : OracleBlock k) (g : BitString → ℕ) (p : Polynomial ℕ)
    (hW : SourceWordCall.WordSolverSpec W g p) {n : ℕ} (hn : 0<n) (a : ℕ) (w : List (ConstraintGate n))
    (r : FirstIndex w) (acc : RationalAccumulator.Ratio) (tail : List RationalAccumulator.Ratio) (C : ℕ)
    (hbit : RationalAccumulator.BitBound C acc (SourceSampleIntegers.middleItems hn a w r++tail)) :
    ∃c,(program W).Executes g (state (k:=k) w a r.val 0 acc)
      (state (k:=k) w a r.val 0 (result hn a w r acc)) c ∧
      c≤(time p).eval ((circuitBits n w).length+a+C) ∧ RationalAccumulator.BitBound C (result hn a w r acc) tail := by
  let rows:=List.ofFn (fun s : SecondIndex w=>SourceSampleIntegers.rowItems hn a w r s)
  let st:=fun i v=>dataState (k:=k) w a r.val i v
  let Inv:=fun i v=>RationalAccumulator.BitBound C v ((rows.drop i).flatten++tail)
  let N:=(circuitBits n w).length+a+C
  have hlen : rows.length=count w := by simp [rows,count,SecondIndex]
  have hcount : count w-1+1=count w := by have h:=count_positive w;omega
  have hbody (i : ℕ) (v : RationalAccumulator.Ratio) (hv : Inv i v) (hi : i<count w-1+1) :
      ∃c,(body W).Executes g (st i v) (st i (SourceFold.stepAt rows [] RationalAccumulator.run i v)) c ∧
        c≤(SourceRow.time p).eval N ∧ Inv (i+1) (SourceFold.stepAt rows [] RationalAccumulator.run i v) := by
    let s : SecondIndex w:=⟨i,by change i<count w;omega⟩
    have hirows : i<rows.length := by omega
    have hrow : rows[i]=SourceSampleIntegers.rowItems hn a w r s := by
      simp only [rows,List.getElem_ofFn]
      rfl
    have hremain:=SourceFold.remaining_rows hirows hv
    rw [hrow] at hremain
    obtain ⟨c,hc,hb,htail⟩:=SourceRow.program_executes W g p hW hn a w r s v ((rows.drop (i+1)).flatten++tail) C hremain
    have hwide:=FramedFor.lift_executes _ g _ _ (List.replicate (count w-1) true) c hc
    have hstep : SourceFold.stepAt rows [] RationalAccumulator.run i v=SourceRow.result hn a w r s v := by
      simp only [SourceFold.stepAt,List.getElem?_eq_getElem hirows,Option.getD_some,hrow,SourceRow.result]
    refine ⟨c,?_,hb,?_⟩
    · simpa only [hstep] using hwide
    · simpa only [Inv,hstep] using htail
  obtain ⟨c,hc,hb,hv⟩:=FramedFor.program_executes (Fin.last (k+66)) (parameterPort k 3) (parameterPort k 24)
    (Ne.symm (FramedFor.body_ne_clock (SourceRow.parameterPort k 24))) (body W) g
    (SourceFold.stepAt rows [] RationalAccumulator.run) st Inv (count w-1) ((SourceRow.time p).eval N)
    (by intro i v;simp [st,dataState])
    (by intro i v;simp [st,parameter_value,SourceSample.store,SourceSample.canonical])
    (by intro i v;simp [st,parameter_value,SourceSample.store])
    (by intro i v
        change Function.update (dataState w a r.val i v) (parameterPort k 3) (true::dataState w a r.val i v (parameterPort k 3))=_
        rw [parameter_value]
        change Function.update (dataState w a r.val i v) (parameterPort k 3) (List.replicate (i+1) true)=_
        rw [update_index])
    (by intro v
        change Function.update (dataState w a r.val (count w-1+1) v) (parameterPort k 3) (List.replicate 0 true)=_
        rw [update_index])
    hbody acc (by simpa only [Inv,List.drop_zero] using hbit)
  have he : UnaryFor.iterate (SourceFold.stepAt rows [] RationalAccumulator.run) 0 (count w-1+1) acc=result hn a w r acc := by
    rw [hcount,←hlen,SourceFold.iterate_rows]
    rfl
  rw [he] at hc hv
  refine ⟨c,hc,?_,?_⟩
  · have hJ : count w≤(N+1)^2 := by
      have hj:=(SourceQueryEnumeration.spectral_count_bounds w a).2
      simp only [SecondIndex,Fintype.card_fin] at hj
      exact hj.trans (Nat.pow_le_pow_left (by dsimp [N];omega) 2)
    have hm:=Nat.mul_le_mul_right ((SourceRow.time p).eval N+5) hJ
    rw [hcount] at hb
    change c≤(time p).eval N
    simp only [time,eval_add,eval_mul,eval_pow,eval_X,eval_ofNat,eval_one]
    omega
  · dsimp only [Inv] at hv
    rw [hcount,←hlen,List.drop_length,List.flatten_nil,List.nil_append] at hv
    exact hv
end HiddenCircuits.Circuit.Runtime.SourceMiddle
