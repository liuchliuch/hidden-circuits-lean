import HiddenCircuits.GraphReduction.Runtime.WordGraph.DriverPolynomial
import HiddenCircuits.GraphReduction.Runtime.WordGraph.DriverAlgebra
import HiddenCircuits.GraphReduction.Runtime.WordGraph.DriverState

namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.Driver
open Complexity OracleBlock BinaryArithmetic Polynomial
set_option maxHeartbeats 700000

def CorrectOracle (g : BitString → ℕ) (w : WordInstance) : Prop :=
  ∀q : Recovery.Index w, answerValue g w q=perfectMatchingCount (Recovery.query w q).2.graph
noncomputable def innerLoop : OracleBlock 97 := DH.Runtime.UnaryFor.program 8 9 cell

 theorem innerLoop_executes (g : BitString → ℕ) (w : WordInstance) (hw : w.word≠[]) (hg : CorrectOracle g w)
    (t : Fin (Recovery.degree w+1)) (a : ℤ×ℤ) (future : List (ℤ×ℤ))
    (hB : RationalAccumulator.BitBound (accumulatorP.eval (wordBits w).length) a (DriverAlgebra.row w t++future)) :
    ∃c, innerLoop.Executes g
      (state w (Recovery.degree w-t.val) t.val (Recovery.height w t) (Recovery.innerDegree w t+1) 0 a [] [] [])
      (state w (Recovery.degree w-t.val) t.val (Recovery.height w t) 0 (Recovery.innerDegree w t+1)
        (RationalAccumulator.run a (DriverAlgebra.row w t)) [] [] []) c ∧
      c≤(Recovery.innerDegree w t+1)*(cellTime.eval (wordBits w).length+5)+1 ∧
      RationalAccumulator.BitBound (accumulatorP.eval (wordBits w).length)
        (RationalAccumulator.run a (DriverAlgebra.row w t)) future := by
  let L := (wordBits w).length
  let row := DriverAlgebra.row w t
  let step := fun (s : ℕ) (a : ℤ×ℤ) => RationalAccumulator.step a (row[s]?.getD (0,1))
  let st := fun (s m : ℕ) (a : ℤ×ℤ) => state w (Recovery.degree w-t.val) t.val (Recovery.height w t) m s a [] [] []
  let Inv := fun (s : ℕ) (a : ℤ×ℤ) => RationalAccumulator.BitBound (accumulatorP.eval L) a (row.drop s++future)
  have hbody : ∀s m a, Inv s a → s+m+1=Recovery.innerDegree w t+1 →
      ∃c, cell.Executes g (st s m a) (st s m (step s a)) c ∧ c≤cellTime.eval L ∧ Inv (s+1) (step s a) := by
    intro s m a hi he
    have hs : s<Recovery.innerDegree w t+1 := by omega
    have hm : m=Recovery.innerDegree w t-s := by omega
    let q : Recovery.Index w := ⟨t,⟨s,hs⟩⟩
    have hget : row[s]?.getD (0,1)=Recovery.ratio w q (perfectMatchingCount (Recovery.query w q).2.graph) :=
      DriverAlgebra.row_get w t s hs
    have hrow : s<row.length := by simpa [row] using hs
    obtain ⟨hitem,hnext⟩ := hi.drop_step hrow
    have hcoeff : RatioCell.componentBound w q (answerValue g w q) (componentP.eval L) := by
      unfold RatioCell.componentBound
      rw [hg q,componentP_eval]
      exact Recovery.ratio_registers_bounded w hw q
    have hratio : (signedBits (Recovery.ratio w q (answerValue g w q)).1).length≤accumulatorP.eval L ∧
        (signedBits (Recovery.ratio w q (answerValue g w q)).2).length≤accumulatorP.eval L := by
      rw [hg q,←hget]
      exact hitem
    obtain ⟨c,hc,hcb⟩ := cell_executes g w q a (componentP.eval L) (accumulatorP.eval L) hcoeff hi.head hratio
    have hcost := actual_cellBound g w hw q (hg q)
    refine ⟨c,?_,hcb.trans hcost,hnext⟩
    rw [hg q] at hc
    simpa only [st,step,q,hm,hget] using hc
  obtain ⟨c,hc,hcb,hinv⟩ := ComplementFor.executes (8:Fin 98) 9 cell g step st Inv (cellTime.eval L) (Recovery.innerDegree w t+1)
    (by intros;rfl)
    (by intro s m a;exact state_update_inner w _ _ _ _ _ _ a [] [] [])
    (by intro s m a;change Function.update (state w _ _ _ m s a [] [] []) 9 (true::List.replicate s true)=_
        rw [←List.replicate_succ,state_update_s])
    hbody 0 (Recovery.innerDegree w t+1) a (by simpa [Inv,row] using hB) (by omega)
  simp only [Nat.zero_add,step,row,DriverAlgebra.inner_iterate] at hc hinv
  refine ⟨c,hc,hcb,?_⟩
  have he : (DriverAlgebra.row w t).drop (Recovery.innerDegree w t+1)=[] := by
    rw [←DriverAlgebra.row_length w t,List.drop_length]
  simpa only [Inv,row,he,List.nil_append] using hinv
end HiddenCircuits.GraphReduction.Runtime.WordGraph.Driver
