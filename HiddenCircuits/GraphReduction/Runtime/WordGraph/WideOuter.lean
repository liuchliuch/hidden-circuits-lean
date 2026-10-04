import HiddenCircuits.GraphReduction.Runtime.WordGraph.WideInner
import HiddenCircuits.GraphReduction.Runtime.WordGraph.DriverRowPrepare
import HiddenCircuits.GraphReduction.Runtime.WordGraph.DriverParameters

/-! Fresh reconstruction of the actual generic outer interpolation loop. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.WideDriver
open Complexity OracleBlock BinaryArithmetic Polynomial
open Driver (heightP innerP degreeP)
open GenericDriver (row rows_get rows_length terms flatten_rows outer_iterate)
set_option maxHeartbeats 700000
noncomputable def rowBody (B : OracleBlock 135) : OracleBlock 135 := seq rowPrepare (seq (innerLoop B) (clear 9))
noncomputable def outerLoop (B : OracleBlock 135) : OracleBlock 135 := DH.Runtime.UnaryFor.program 5 6 (rowBody B)
noncomputable def rowBound (w : WordInstance) (C : ℕ) : ℕ :=
  let L := (wordBits w).length
  5*L+(10*L+9)*heightP.eval L+12+(innerP.eval L+1)*(C+5)+innerP.eval L+7
noncomputable def loopBound (w : WordInstance) (C : ℕ) : ℕ :=
  (degreeP.eval (wordBits w).length+1)*(rowBound w C+5)+1
noncomputable def rowStep (w : WordInstance) (term : Recovery.Index w → ℤ×ℤ) (t : ℕ) (a : ℕ×(ℤ×ℤ)) : ℕ×(ℤ×ℤ) :=
  (w.word.length+a.1,RationalAccumulator.run a.2 ((GenericDriver.rows w term)[t]?.getD []))

lemma row_iterate (w : WordInstance) (term : Recovery.Index w → ℤ×ℤ) (i n h : ℕ) (a : ℤ×ℤ) :
    DH.Runtime.UnaryFor.iterate (rowStep w term) i n (h,a)=
      (h+n*w.word.length,DH.Runtime.UnaryFor.iterate
        (fun t a => RationalAccumulator.run a ((GenericDriver.rows w term)[t]?.getD [])) i n a) := by
  induction n generalizing i h a with
  | zero => simp [DH.Runtime.UnaryFor.iterate]
  | succ n ih =>
    rw [DH.Runtime.UnaryFor.iterate,ih,DH.Runtime.UnaryFor.iterate]
    simp only [rowStep]
    congr 1
    ring

 theorem outerLoop_executes (B : OracleBlock 135) (g : BitString → ℕ) (w : WordInstance)
    (term : Recovery.Index w → ℤ×ℤ) (BA C : ℕ) (hSpec : CellSpec B g w term BA C)
    (a : ℤ×ℤ) (hB : RationalAccumulator.BitBound BA a (terms w term)) :
    ∃c, (outerLoop B).Executes g (state 38 w (Recovery.degree w+1) 0 0 0 0 a [] [] [])
      (state 38 w 0 (Recovery.degree w+1) ((Recovery.degree w+1)*w.word.length) 0 0
        (RationalAccumulator.run a (terms w term)) [] [] []) c ∧
      c ≤ loopBound w C ∧ RationalAccumulator.BitBound BA (RationalAccumulator.run a (terms w term)) [] := by
  let L := (wordBits w).length
  let rows := GenericDriver.rows w term
  let st := fun t m (a : ℕ×(ℤ×ℤ)) => state 38 w m t a.1 0 0 a.2 [] [] []
  let Inv := fun t (a : ℕ×(ℤ×ℤ)) => a.1=t*w.word.length ∧
    RationalAccumulator.BitBound BA a.2 (rows.drop t).flatten
  have hbody : ∀t m a, Inv t a → t+m+1=Recovery.degree w+1 →
      ∃c, (rowBody B).Executes g (st t m a) (st t m (rowStep w term t a)) c ∧
        c≤rowBound w C ∧ Inv (t+1) (rowStep w term t a) := by
    intro t m a hi he
    have ht : t<Recovery.degree w+1 := by omega
    have hm : m=Recovery.degree w-t := by omega
    let tf : Fin (Recovery.degree w+1) := ⟨t,ht⟩
    let future := (rows.drop (t+1)).flatten
    have hlen : t<rows.length := by simpa [rows] using ht
    have hrow : (GenericDriver.rows w term)[t]?.getD []=row w term tf := rows_get w term t ht
    have hrow' : rows[t]=row w term tf := by
      have hx := hrow
      change rows[t]?.getD []=row w term tf at hx
      simpa only [List.getElem?_eq_getElem hlen,Option.getD_some] using hx
    have hterms : RationalAccumulator.BitBound BA a.2 (row w term tf++future) := by
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
    obtain ⟨b,hb,hbb,hnext⟩ := innerLoop_executes B g w term BA C hSpec tf a.2 future hterms
    have hz := clearInnerIndex_executes g w m t (Recovery.height w tf) (Recovery.innerDegree w tf+1)
      (RationalAccumulator.run a.2 (row w term tf))
    rw [hm] at hp hz
    have hc := seq_executes _ _ g hp (seq_executes _ _ g hb hz)
    refine ⟨_,by simpa only [st,rowStep,hm,hH,hrow] using hc,?_,?_⟩
    · have hpL : w.particles≤L := by have := wordBits_length_lower w;dsimp [L];omega
      have hlL : w.word.length≤L := by have := wordBits_length_lower w;dsimp [L];omega
      have hheight : Recovery.height w tf≤heightP.eval L := by simpa [L] using (Recovery.parameter_bounds w tf).2.1
      have hinner : Recovery.innerDegree w tf≤ innerP.eval L := by simpa [L] using (Recovery.parameter_bounds w tf).2.2
      simp only [rowBound,eval_add,eval_mul,eval_X,eval_ofNat,eval_one]
      have h₁ : 5*w.word.length+(10*w.particles+9)*Recovery.height w tf+12≤5*L+(10*L+9)*heightP.eval L+12 := by gcongr
      have h₂ : (Recovery.innerDegree w tf+1)*(C+5)+1≤(innerP.eval L+1)*(C+5)+1 := by gcongr
      change b≤(Recovery.innerDegree w tf+1)*(C+5)+1 at hbb
      dsimp only [L] at *
      omega
    · constructor
      · change w.word.length+a.1=(t+1)*w.word.length
        rw [hi.1];ring
      · simpa only [Inv,rowStep,hrow] using hnext
  obtain ⟨c,hc,hcb,hinv⟩ := ComplementFor.executes (5:Fin 136) 6 (rowBody B) g (rowStep w term) st Inv
    (rowBound w C) (Recovery.degree w+1)
    (by intros;rfl)
    (by intro t m a;exact state_update_outer w _ _ _ _ _ _ a.2 [] [] [])
    (by intro t m a;change Function.update (state 38 w _ t _ _ _ _ [] [] []) 6 (true::List.replicate t true)=_
        rw [←List.replicate_succ,state_update_t])
    hbody 0 (Recovery.degree w+1) (0,a)
    (by refine ⟨by simp,?_⟩;simpa [Inv,rows,flatten_rows] using hB) (by omega)
  simp only [Nat.zero_add,row_iterate,outer_iterate] at hc hinv
  refine ⟨c,hc,?_,?_⟩
  · have hd : Recovery.degree w≤degreeP.eval L := by simpa [L] using (Recovery.parameter_bounds w ⟨0,by omega⟩).1
    apply hcb.trans
    simp only [loopBound,eval_add,eval_mul,eval_one,eval_ofNat]
    gcongr
  · have he : (GenericDriver.rows w term).drop (Recovery.degree w+1)=[] := by
      rw [←rows_length w term,List.drop_length]
    simpa only [Inv,rows,he,List.flatten_nil] using hinv.2
end HiddenCircuits.GraphReduction.Runtime.WordGraph.WideDriver
