import HiddenCircuits.Circuit.Runtime.SpectralDeltaLoopCore
import HiddenCircuits.Circuit.Runtime.SpectralDeltaCellRuntime

/-! Actual second-spectral iteration, charging every native Delta cell and
carrying a single rational-prefix bit bound through the remaining item list. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralDeltaLoopInner
open Complexity OracleBlock BinaryArithmetic Polynomial SourceQueryRecovery
open HiddenCircuits.DH.Runtime

noncomputable def body : OracleBlock 64 := rename SpectralDeltaCell.program (FramedFor.embedding 63)
noncomputable def program : OracleBlock 65 :=
  FramedFor.program (Fin.last 64) (parameterPort 3) (parameterPort 24)
    (Ne.symm (FramedFor.body_ne_clock 24)) body
noncomputable def result {n : ℕ} (w : List (ConstraintGate n)) (r : FirstIndex w) (acc : RationalAccumulator.Ratio) : RationalAccumulator.Ratio :=
  RationalAccumulator.run acc (SpectralDelta.row w r)
noncomputable def cellTime : Polynomial ℕ := SpectralDeltaCell.time.comp SourceQueryStorage.boundedStorageSize
noncomputable def time : Polynomial ℕ := (X+1)^2*(cellTime+5)+6*(X+1)^2+12

set_option maxHeartbeats 1200000 in
theorem program_executes (g : BitString → ℕ) (hg : DeltaOracle g) {n : ℕ} (w : List (ConstraintGate n))
    (r : FirstIndex w) (acc : RationalAccumulator.Ratio) (tail : List RationalAccumulator.Ratio) (C : ℕ)
    (hbit : RationalAccumulator.BitBound C acc (SpectralDelta.row w r++tail)) :
    ∃c,program.Executes g (state w r.val 0 acc) (state w r.val 0 (result w r acc)) c ∧
      c≤time.eval ((circuitBits n w).length+C) ∧ RationalAccumulator.BitBound C (result w r acc) tail := by
  let xs:=SpectralDelta.row w r
  let st:=fun i v=>dataState w r.val i v
  let Inv:=fun i v=>RationalAccumulator.BitBound C v (xs.drop i++tail)
  let N:=(circuitBits n w).length+C
  have hlen : xs.length=count w := by simp [xs,SpectralDelta.row,count,SecondIndex]
  have hcount : count w-1+1=count w := by have h:=count_positive w;omega
  have hbody (i : ℕ) (v : RationalAccumulator.Ratio) (hv : Inv i v) (hi : i<count w-1+1) :
      ∃c,body.Executes g (st i v) (st i (SourceFold.stepAt xs (0,1) RationalAccumulator.step i v)) c ∧
        c≤cellTime.eval N ∧ Inv (i+1) (SourceFold.stepAt xs (0,1) RationalAccumulator.step i v) := by
    let s : SecondIndex w:=⟨i,by change i<count w;omega⟩
    have hil : i<xs.length := by omega
    have hvnext:=RationalAccumulator.BitBound.drop_step hv hil
    obtain ⟨c,hc,hb⟩:=SpectralDeltaCell.program_executes g hg w r s v
      (SourceQueryStorage.boundedStorageSize.eval N) (storage_bound w C r s v hv.head)
    have hwide:=FramedFor.lift_executes _ g _ _ (List.replicate (count w-1) true) c hc
    have hitem : xs[i]?.getD (0,1)=SpectralDelta.item w r s := by
      rw [List.getElem?_eq_getElem hil,Option.getD_some]
      simp only [xs,SpectralDelta.row,List.getElem_ofFn]
      rfl
    have hstep : SourceFold.stepAt xs (0,1) RationalAccumulator.step i v=RationalAccumulator.step v (SpectralDelta.item w r s) := by
      simp only [SourceFold.stepAt,hitem]
    refine ⟨c,?_,?_,?_⟩
    · simpa only [hstep] using hwide
    · simpa only [cellTime,eval_comp] using hb
    · exact hvnext.2
  obtain ⟨c,hc,hb,hv⟩:=FramedFor.program_executes (Fin.last 64) (parameterPort 3) (parameterPort 24)
    (Ne.symm (FramedFor.body_ne_clock 24)) body g
    (SourceFold.stepAt xs (0,1) RationalAccumulator.step) st Inv (count w-1) (cellTime.eval N)
    (by intro i v;simp only [st,dataState,FramedFor.frame_clock])
    (by intro i v;simp [st,SourceSample.store,SourceSample.canonical])
    (by intro i v;simp [st,SourceSample.store])
    (by intro i v
        change Function.update (dataState w r.val i v) (parameterPort 3) (true::dataState w r.val i v (parameterPort 3))=_
        rw [parameter_value]
        change Function.update (dataState w r.val i v) (parameterPort 3) (List.replicate (i+1) true)=_
        rw [update_index])
    (by intro v
        change Function.update (dataState w r.val (count w-1+1) v) (parameterPort 3) (List.replicate 0 true)=_
        rw [update_index])
    hbody acc (by simpa only [Inv,List.drop_zero] using hbit)
  have he : UnaryFor.iterate (SourceFold.stepAt xs (0,1) RationalAccumulator.step) 0 (count w-1+1) acc=result w r acc := by
    rw [hcount,←hlen,SourceFold.iterate_all]
    rfl
  rw [he] at hc hv
  refine ⟨c,hc,?_,?_⟩
  · have hJ : count w≤(N+1)^2 := by
      have hj:=(SourceQueryEnumeration.spectral_count_bounds w 0).2
      simp only [Nat.add_zero,SecondIndex,Fintype.card_fin] at hj
      exact hj.trans (Nat.pow_le_pow_left (by dsimp [N];omega) 2)
    have hm:=Nat.mul_le_mul_right (cellTime.eval N+5) hJ
    rw [hcount] at hb
    change c≤time.eval N
    simp only [time,eval_add,eval_mul,eval_pow,eval_X,eval_ofNat,eval_one]
    omega
  · dsimp only [Inv] at hv
    rw [hcount,←hlen,List.drop_length,List.nil_append] at hv
    exact hv
end HiddenCircuits.Circuit.Runtime.SpectralDeltaLoopInner
