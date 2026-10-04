import HiddenCircuits.Circuit.Runtime.SpectralDeltaLoopInner

/-! The actual outer spectral loop completes the two-dimensional native
Delta recovery, with polynomial cost for all queries, answers and arithmetic. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralDeltaLoop
open Complexity OracleBlock BinaryArithmetic Polynomial SourceQueryRecovery
open HiddenCircuits.DH.Runtime

noncomputable def body : OracleBlock 66 := rename SpectralDeltaLoopInner.program (FramedFor.embedding 65)
noncomputable def program : OracleBlock 67 :=
  FramedFor.program (Fin.last 66) (parameterPort 2) (parameterPort 24)
    (Ne.symm (FramedFor.body_ne_clock (SpectralDeltaLoopInner.outerPort 24))) body
noncomputable def result {n : ℕ} (w : List (ConstraintGate n)) (acc : RationalAccumulator.Ratio) : RationalAccumulator.Ratio :=
  RationalAccumulator.run acc (SpectralDelta.items w)
noncomputable def time : Polynomial ℕ := (X+1)^2*(SpectralDeltaLoopInner.time+5)+6*(X+1)^2+12

set_option maxHeartbeats 1200000 in
theorem program_executes (g : BitString → ℕ) (hg : DeltaOracle g) {n : ℕ} (w : List (ConstraintGate n))
    (acc : RationalAccumulator.Ratio) (tail : List RationalAccumulator.Ratio) (C : ℕ)
    (hbit : RationalAccumulator.BitBound C acc (SpectralDelta.items w++tail)) :
    ∃c,program.Executes g (state w 0 acc) (state w 0 (result w acc)) c ∧
      c≤time.eval ((circuitBits n w).length+C) ∧ RationalAccumulator.BitBound C (result w acc) tail := by
  let rows:=List.ofFn (fun r : FirstIndex w=>SpectralDelta.row w r)
  let st:=fun i v=>dataState w i v
  let Inv:=fun i v=>RationalAccumulator.BitBound C v ((rows.drop i).flatten++tail)
  let N:=(circuitBits n w).length+C
  have hlen : rows.length=count w := by simp [rows,count,FirstIndex]
  have hcount : count w-1+1=count w := by have h:=count_positive w;omega
  have hbody (i : ℕ) (v : RationalAccumulator.Ratio) (hv : Inv i v) (hi : i<count w-1+1) :
      ∃c,body.Executes g (st i v) (st i (SourceFold.stepAt rows [] RationalAccumulator.run i v)) c ∧
        c≤SpectralDeltaLoopInner.time.eval N ∧ Inv (i+1) (SourceFold.stepAt rows [] RationalAccumulator.run i v) := by
    let r : FirstIndex w:=⟨i,by change i<count w;omega⟩
    have hirows : i<rows.length := by omega
    have hrow : rows[i]=SpectralDelta.row w r := by
      simp only [rows,List.getElem_ofFn]
      rfl
    have hremain:=SourceFold.remaining_rows hirows hv
    rw [hrow] at hremain
    obtain ⟨c,hc,hb,htail⟩:=SpectralDeltaLoopInner.program_executes g hg w r v ((rows.drop (i+1)).flatten++tail) C hremain
    have hwide:=FramedFor.lift_executes _ g _ _ (List.replicate (count w-1) true) c hc
    have hstep : SourceFold.stepAt rows [] RationalAccumulator.run i v=SpectralDeltaLoopInner.result w r v := by
      simp only [SourceFold.stepAt,List.getElem?_eq_getElem hirows,Option.getD_some,hrow,SpectralDeltaLoopInner.result]
    refine ⟨c,?_,hb,?_⟩
    · simpa only [hstep] using hwide
    · simpa only [Inv,hstep] using htail
  obtain ⟨c,hc,hb,hv⟩:=FramedFor.program_executes (Fin.last 66) (parameterPort 2) (parameterPort 24)
    (Ne.symm (FramedFor.body_ne_clock (SpectralDeltaLoopInner.outerPort 24))) body g
    (SourceFold.stepAt rows [] RationalAccumulator.run) st Inv (count w-1) (SpectralDeltaLoopInner.time.eval N)
    (by intro i v;simp only [st,dataState,FramedFor.frame_clock])
    (by intro i v;simp [st,SourceSample.store,SourceSample.canonical])
    (by intro i v;simp [st,SourceSample.store])
    (by intro i v
        change Function.update (dataState w i v) (parameterPort 2) (true::dataState w i v (parameterPort 2))=_
        rw [parameter_value]
        change Function.update (dataState w i v) (parameterPort 2) (List.replicate (i+1) true)=_
        rw [update_index])
    (by intro v
        change Function.update (dataState w (count w-1+1) v) (parameterPort 2) (List.replicate 0 true)=_
        rw [update_index])
    hbody acc (by simpa only [Inv,List.drop_zero] using hbit)
  have he : UnaryFor.iterate (SourceFold.stepAt rows [] RationalAccumulator.run) 0 (count w-1+1) acc=result w acc := by
    rw [hcount,←hlen,SourceFold.iterate_rows]
    rfl
  rw [he] at hc hv
  refine ⟨c,hc,?_,?_⟩
  · have hJ : count w≤(N+1)^2 := by
      have hj:=(SourceQueryEnumeration.spectral_count_bounds w 0).1
      simp only [Nat.add_zero,FirstIndex,Fintype.card_fin] at hj
      exact hj.trans (Nat.pow_le_pow_left (by dsimp [N];omega) 2)
    have hm:=Nat.mul_le_mul_right (SpectralDeltaLoopInner.time.eval N+5) hJ
    rw [hcount] at hb
    change c≤time.eval N
    simp only [time,eval_add,eval_mul,eval_pow,eval_X,eval_ofNat,eval_one]
    omega
  · dsimp only [Inv] at hv
    rw [hcount,←hlen,List.drop_length,List.flatten_nil,List.nil_append] at hv
    exact hv
end HiddenCircuits.Circuit.Runtime.SpectralDeltaLoop
