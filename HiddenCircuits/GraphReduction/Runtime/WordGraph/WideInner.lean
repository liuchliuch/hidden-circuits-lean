import HiddenCircuits.GraphReduction.Runtime.WordGraph.GenericRows
import HiddenCircuits.GraphReduction.Runtime.WordGraph.WideState

/-! Reusable actual interpolation loop. Its body is a finite block, and each
concrete target instantiation must prove that block's exact execution contract. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.WideDriver
open Complexity OracleBlock BinaryArithmetic
open GenericDriver (row row_get row_length inner_iterate terms)

 def CellSpec (B : OracleBlock 135) (g : BitString → ℕ) (w : WordInstance)
    (term : Recovery.Index w → ℤ×ℤ) (BA C : ℕ) : Prop :=
  ∀q a, ((signedBits a.1).length≤BA ∧ (signedBits a.2).length≤BA) →
    ((signedBits (term q).1).length≤BA ∧ (signedBits (term q).2).length≤BA) →
    ∃c, B.Executes g
      (state 38 w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val a [] [] [])
      (state 38 w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val
        (RationalAccumulator.step a (term q)) [] [] []) c ∧ c≤C

noncomputable def innerLoop (B : OracleBlock 135) : OracleBlock 135 := DH.Runtime.UnaryFor.program 8 9 B

 theorem innerLoop_executes (B : OracleBlock 135) (g : BitString → ℕ) (w : WordInstance)
    (term : Recovery.Index w → ℤ×ℤ) (BA C : ℕ) (hSpec : CellSpec B g w term BA C)
    (t : Fin (Recovery.degree w+1)) (a : ℤ×ℤ) (future : List (ℤ×ℤ))
    (hB : RationalAccumulator.BitBound BA a (row w term t++future)) :
    ∃c, (innerLoop B).Executes g
      (state 38 w (Recovery.degree w-t.val) t.val (Recovery.height w t) (Recovery.innerDegree w t+1) 0 a [] [] [])
      (state 38 w (Recovery.degree w-t.val) t.val (Recovery.height w t) 0 (Recovery.innerDegree w t+1)
        (RationalAccumulator.run a (row w term t)) [] [] []) c ∧
      c≤(Recovery.innerDegree w t+1)*(C+5)+1 ∧
      RationalAccumulator.BitBound BA (RationalAccumulator.run a (row w term t)) future := by
  let r := row w term t
  let step := fun (s : ℕ) (a : ℤ×ℤ) => RationalAccumulator.step a (r[s]?.getD (0,1))
  let st := fun (s m : ℕ) (a : ℤ×ℤ) => state 38 w (Recovery.degree w-t.val) t.val (Recovery.height w t) m s a [] [] []
  let Inv := fun (s : ℕ) (a : ℤ×ℤ) => RationalAccumulator.BitBound BA a (r.drop s++future)
  have hbody : ∀s m a, Inv s a → s+m+1=Recovery.innerDegree w t+1 →
      ∃c, B.Executes g (st s m a) (st s m (step s a)) c ∧ c≤C ∧ Inv (s+1) (step s a) := by
    intro s m a hi he
    have hs : s<Recovery.innerDegree w t+1 := by omega
    have hm : m=Recovery.innerDegree w t-s := by omega
    let q : Recovery.Index w := ⟨t,⟨s,hs⟩⟩
    have hget : r[s]?.getD (0,1)=term q := row_get w term t s hs
    have hr : s<r.length := by simpa [r] using hs
    obtain ⟨hitem,hnext⟩ := hi.drop_step hr
    have hterm : (signedBits (term q).1).length≤BA ∧ (signedBits (term q).2).length≤BA := by rw [←hget];exact hitem
    obtain ⟨c,hc,hcb⟩ := hSpec q a hi.head hterm
    exact ⟨c,by simpa only [st,step,q,hm,hget] using hc,hcb,hnext⟩
  obtain ⟨c,hc,hcb,hinv⟩ := ComplementFor.executes (8:Fin 136) 9 B g step st Inv C (Recovery.innerDegree w t+1)
    (by intros;rfl)
    (by intro s m a;exact state_update_inner w _ _ _ _ _ _ a [] [] [])
    (by intro s m a;change Function.update (state 38 w _ _ _ m s a [] [] []) 9 (true::List.replicate s true)=_
        rw [←List.replicate_succ,state_update_s])
    hbody 0 (Recovery.innerDegree w t+1) a (by simpa [Inv,r] using hB) (by omega)
  simp only [Nat.zero_add,step,r,inner_iterate] at hc hinv
  refine ⟨c,hc,hcb,?_⟩
  have he : (row w term t).drop (Recovery.innerDegree w t+1)=[] := by rw [←row_length w term t,List.drop_length]
  simpa only [Inv,r,he,List.nil_append] using hinv
end HiddenCircuits.GraphReduction.Runtime.WordGraph.WideDriver
