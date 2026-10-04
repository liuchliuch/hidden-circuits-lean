import HiddenCircuits.GraphReduction.Runtime.WordGraph.DriverInner
import HiddenCircuits.GraphReduction.Runtime.WordGraph.DriverRowPrepare

namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.Driver
open Complexity OracleBlock BinaryArithmetic Polynomial
set_option maxHeartbeats 700000

noncomputable def rowBody : OracleBlock 97 := seq rowPrepare (seq innerLoop (clear 9))
noncomputable def outerLoop : OracleBlock 97 := DH.Runtime.UnaryFor.program 5 6 rowBody
noncomputable def rowTime : Polynomial ℕ :=
  5*X+(10*X+9)*heightP+12+(innerP+1)*(cellTime+5)+innerP+7
noncomputable def loopTime : Polynomial ℕ := (degreeP+1)*(rowTime+5)+1

noncomputable def rowStep (w : WordInstance) (t : ℕ) (a : ℕ×(ℤ×ℤ)) : ℕ×(ℤ×ℤ) :=
  (w.word.length+a.1,RationalAccumulator.run a.2 ((DriverAlgebra.rows w)[t]?.getD []))

lemma row_iterate (w : WordInstance) (i n h : ℕ) (a : ℤ×ℤ) :
    DH.Runtime.UnaryFor.iterate (rowStep w) i n (h,a)=
      (h+n*w.word.length,DH.Runtime.UnaryFor.iterate
        (fun t a => RationalAccumulator.run a ((DriverAlgebra.rows w)[t]?.getD [])) i n a) := by
  induction n generalizing i h a with
  | zero => simp [DH.Runtime.UnaryFor.iterate]
  | succ n ih =>
    rw [DH.Runtime.UnaryFor.iterate,ih,DH.Runtime.UnaryFor.iterate]
    simp only [rowStep]
    congr 1
    ring

lemma initialBitBound (w : WordInstance) (hw : w.word≠[]) :
    RationalAccumulator.BitBound (accumulatorP.eval (wordBits w).length) (0,1) (Recovery.terms w) := by
  have h := RationalAccumulator.bitBound_of_abs (0,1) (Recovery.terms w) 1 (Recovery.termExponent (wordBits w).length)
    (by constructor <;> decide) (by
      intro b hb
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hb
      exact Recovery.ratio_bound w hw q)
  apply h.mono
  rw [accumulatorP_eval]
  have hl := Recovery.terms_length_bound w
  nlinarith

 theorem outerLoop_executes (g : BitString → ℕ) (w : WordInstance) (hw : w.word≠[]) (hg : CorrectOracle g w) :
    ∃c, outerLoop.Executes g (state w (Recovery.degree w+1) 0 0 0 0 (0,1) [] [] [])
      (state w 0 (Recovery.degree w+1) ((Recovery.degree w+1)*w.word.length) 0 0
        (RationalAccumulator.run (0,1) (Recovery.terms w)) [] [] []) c ∧
      c≤loopTime.eval (wordBits w).length ∧
      RationalAccumulator.BitBound (accumulatorP.eval (wordBits w).length)
        (RationalAccumulator.run (0,1) (Recovery.terms w)) [] := by
  let L := (wordBits w).length
  let rows := DriverAlgebra.rows w
  let st := fun t m (a : ℕ×(ℤ×ℤ)) => state w m t a.1 0 0 a.2 [] [] []
  let Inv := fun t (a : ℕ×(ℤ×ℤ)) => a.1=t*w.word.length ∧
    RationalAccumulator.BitBound (accumulatorP.eval L) a.2 (rows.drop t).flatten
  have hbody : ∀t m a, Inv t a → t+m+1=Recovery.degree w+1 →
      ∃c, rowBody.Executes g (st t m a) (st t m (rowStep w t a)) c ∧
        c≤rowTime.eval L ∧ Inv (t+1) (rowStep w t a) := by
    intro t m a hi he
    have ht : t<Recovery.degree w+1 := by omega
    have hm : m=Recovery.degree w-t := by omega
    let tf : Fin (Recovery.degree w+1) := ⟨t,ht⟩
    let future := (rows.drop (t+1)).flatten
    have hlen : t<rows.length := by simpa [rows] using ht
    have hrow : (DriverAlgebra.rows w)[t]?.getD []=DriverAlgebra.row w tf := DriverAlgebra.rows_get w t ht
    have hrow' : rows[t]=DriverAlgebra.row w tf := by
      have hx := hrow
      change rows[t]?.getD []=DriverAlgebra.row w tf at hx
      simpa only [List.getElem?_eq_getElem hlen,Option.getD_some] using hx
    have hterms : RationalAccumulator.BitBound (accumulatorP.eval L) a.2 (DriverAlgebra.row w tf++future) := by
      have hh := hi.2
      rw [List.drop_eq_getElem_cons hlen,List.flatten_cons,hrow'] at hh
      exact hh
    have hH : w.word.length+a.1=Recovery.height w tf := by
      rw [hi.1]
      simp only [Recovery.height,sampleWord_length,tf]
      ring
    have hp := rowPrepare_executes g w m t a.1 a.2
    rw [hH] at hp
    have hE : 2*w.particles*Recovery.height w tf=Recovery.innerDegree w tf := rfl
    rw [hE] at hp
    obtain ⟨b,hb,hbb,hnext⟩ := innerLoop_executes g w hw hg tf a.2 future hterms
    have hz := clearInnerIndex_executes g w m t (Recovery.height w tf) (Recovery.innerDegree w tf+1)
      (RationalAccumulator.run a.2 (DriverAlgebra.row w tf))
    rw [hm] at hp hz
    have hc := seq_executes _ _ g hp (seq_executes _ _ g hb hz)
    refine ⟨_,by simpa only [st,rowStep,hm,hH,hrow] using hc,?_,?_⟩
    · have hpL : w.particles≤L := by have := wordBits_length_lower w;dsimp [L];omega
      have hlL : w.word.length≤L := by have := wordBits_length_lower w;dsimp [L];omega
      have hheight : Recovery.height w tf≤heightP.eval L := by simpa [L] using (Recovery.parameter_bounds w tf).2.1
      have hinner : Recovery.innerDegree w tf≤ innerP.eval L := by simpa [L] using (Recovery.parameter_bounds w tf).2.2
      simp only [rowTime,eval_add,eval_mul,eval_X,eval_ofNat,eval_one]
      have h₁ : 5*w.word.length+(10*w.particles+9)*Recovery.height w tf+12≤5*L+(10*L+9)*heightP.eval L+12 := by gcongr
      have h₂ : (Recovery.innerDegree w tf+1)*(cellTime.eval L+5)+1≤(innerP.eval L+1)*(cellTime.eval L+5)+1 := by gcongr
      change b≤(Recovery.innerDegree w tf+1)*(cellTime.eval L+5)+1 at hbb
      omega
    · constructor
      · change w.word.length+a.1=(t+1)*w.word.length
        rw [hi.1];ring
      · simpa only [Inv,rowStep,hrow] using hnext
  obtain ⟨c,hc,hcb,hinv⟩ := ComplementFor.executes (5:Fin 98) 6 rowBody g (rowStep w) st Inv
    (rowTime.eval L) (Recovery.degree w+1)
    (by intros;rfl)
    (by intro t m a;exact state_update_outer w _ _ _ _ _ _ a.2 [] [] [])
    (by intro t m a;change Function.update (state w _ t _ _ _ _ [] [] []) 6 (true::List.replicate t true)=_
        rw [←List.replicate_succ,state_update_t])
    hbody 0 (Recovery.degree w+1) (0,(0,1))
    (by refine ⟨by simp,?_⟩;simpa [Inv,rows,DriverAlgebra.flatten_rows] using initialBitBound w hw) (by omega)
  simp only [Nat.zero_add,row_iterate,DriverAlgebra.outer_iterate] at hc hinv
  refine ⟨c,hc,?_,?_⟩
  · have hd : Recovery.degree w≤degreeP.eval L := by simpa [L] using (Recovery.parameter_bounds w ⟨0,by omega⟩).1
    apply hcb.trans
    simp only [loopTime,eval_add,eval_mul,eval_one,eval_ofNat]
    gcongr
  · have he : (DriverAlgebra.rows w).drop (Recovery.degree w+1)=[] := by
      rw [←DriverAlgebra.rows_length w,List.drop_length]
    simpa only [Inv,rows,he,List.flatten_nil] using hinv.2
end HiddenCircuits.GraphReduction.Runtime.WordGraph.Driver
