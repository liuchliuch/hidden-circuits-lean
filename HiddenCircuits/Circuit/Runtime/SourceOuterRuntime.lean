import HiddenCircuits.Circuit.Runtime.SourceOuterFrame

/-! Actual full nested spectral/geometric source execution,
with every scalar, physical word, oracle call, integer operation and loop charged. -/
namespace HiddenCircuits.Circuit.Runtime.SourceOuter
open HiddenCircuits.Complexity OracleBlock BinaryArithmetic Polynomial SourceQueryRecovery
open HiddenCircuits.DH.Runtime

set_option maxHeartbeats 1200000 in
theorem program_executes {k : ℕ} (W : OracleBlock k) (g : BitString → ℕ) (p : Polynomial ℕ)
    (hW : SourceWordCall.WordSolverSpec W g p) {n : ℕ} (hn : 0<n) (a : ℕ) (w : List (ConstraintGate n))
    (acc : RationalAccumulator.Ratio) (tail : List RationalAccumulator.Ratio) (C : ℕ)
    (hbit : RationalAccumulator.BitBound C acc (SourceSampleIntegers.items hn a w++tail)) :
    ∃c,(program W).Executes g (state (k:=k) w a 0 acc) (state (k:=k) w a 0 (result hn a w acc)) c ∧
      c≤(time p).eval ((circuitBits n w).length+a+C) ∧ RationalAccumulator.BitBound C (result hn a w acc) tail := by
  let rows:=List.ofFn (fun r : FirstIndex w=>SourceSampleIntegers.middleItems hn a w r)
  let st:=fun i v=>dataState (k:=k) w a i v
  let Inv:=fun i v=>RationalAccumulator.BitBound C v ((rows.drop i).flatten++tail)
  let N:=(circuitBits n w).length+a+C
  have hlen : rows.length=count w := by simp [rows,count,FirstIndex]
  have hcount : count w-1+1=count w := by have h:=count_positive w;omega
  have hbody (i : ℕ) (v : RationalAccumulator.Ratio) (hv : Inv i v) (hi : i<count w-1+1) :
      ∃c,(body W).Executes g (st i v) (st i (SourceFold.stepAt rows [] RationalAccumulator.run i v)) c ∧
        c≤(SourceMiddle.time p).eval N ∧ Inv (i+1) (SourceFold.stepAt rows [] RationalAccumulator.run i v) := by
    let r : FirstIndex w:=⟨i,by change i<count w;omega⟩
    have hirows : i<rows.length := by omega
    have hrow : rows[i]=SourceSampleIntegers.middleItems hn a w r := by
      simp only [rows,List.getElem_ofFn]
      rfl
    have hremain:=SourceFold.remaining_rows hirows hv
    rw [hrow] at hremain
    obtain ⟨c,hc,hb,htail⟩:=SourceMiddle.program_executes W g p hW hn a w r v ((rows.drop (i+1)).flatten++tail) C hremain
    have hwide:=FramedFor.lift_executes _ g _ _ (List.replicate (count w-1) true) c hc
    have hstep : SourceFold.stepAt rows [] RationalAccumulator.run i v=SourceMiddle.result hn a w r v := by
      simp only [SourceFold.stepAt,List.getElem?_eq_getElem hirows,Option.getD_some,hrow,SourceMiddle.result]
    refine ⟨c,?_,hb,?_⟩
    · simpa only [hstep] using hwide
    · simpa only [Inv,hstep] using htail
  obtain ⟨c,hc,hb,hv⟩:=FramedFor.program_executes (Fin.last (k+68)) (parameterPort k 2) (parameterPort k 24)
    (Ne.symm (FramedFor.body_ne_clock (SourceMiddle.outerPort k 24))) (body W) g
    (SourceFold.stepAt rows [] RationalAccumulator.run) st Inv (count w-1) ((SourceMiddle.time p).eval N)
    (by intro i v;simp [st,dataState])
    (by intro i v;simp [st,parameter_value,SourceSample.store,SourceSample.canonical])
    (by intro i v;simp [st,parameter_value,SourceSample.store])
    (by intro i v
        change Function.update (dataState w a i v) (parameterPort k 2) (true::dataState w a i v (parameterPort k 2))=_
        rw [parameter_value]
        change Function.update (dataState w a i v) (parameterPort k 2) (List.replicate (i+1) true)=_
        rw [update_index])
    (by intro v
        change Function.update (dataState w a (count w-1+1) v) (parameterPort k 2) (List.replicate 0 true)=_
        rw [update_index])
    hbody acc (by simpa only [Inv,List.drop_zero] using hbit)
  have he : UnaryFor.iterate (SourceFold.stepAt rows [] RationalAccumulator.run) 0 (count w-1+1) acc=result hn a w acc := by
    rw [hcount,←hlen,SourceFold.iterate_rows]
    rfl
  rw [he] at hc hv
  refine ⟨c,hc,?_,?_⟩
  · have hJ : count w≤(N+1)^2 := by
      have hj:=(SourceQueryEnumeration.spectral_count_bounds w a).1
      simp only [FirstIndex,Fintype.card_fin] at hj
      exact hj.trans (Nat.pow_le_pow_left (by dsimp [N];omega) 2)
    have hm:=Nat.mul_le_mul_right ((SourceMiddle.time p).eval N+5) hJ
    rw [hcount] at hb
    change c≤(time p).eval N
    simp only [time,eval_add,eval_mul,eval_pow,eval_X,eval_ofNat,eval_one]
    omega
  · dsimp only [Inv] at hv
    rw [hcount,←hlen,List.drop_length,List.flatten_nil,List.nil_append] at hv
    exact hv
end HiddenCircuits.Circuit.Runtime.SourceOuter
