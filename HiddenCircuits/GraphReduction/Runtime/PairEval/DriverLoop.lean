import HiddenCircuits.GraphReduction.Runtime.PairEval.DriverState
import HiddenCircuits.GraphReduction.Runtime.PairEval.GraphRecovery
import HiddenCircuits.GraphReduction.Runtime.WordGraph.DriverAlgebra

/-! A single physical unary loop schedules every probe once; its invariant
tracks the actual integer rational accumulator and all future summands. -/
namespace HiddenCircuits.GraphReduction.Runtime.PairEval.Driver
open Complexity OracleBlock BinaryArithmetic WordGraph
set_option maxHeartbeats 700000

lemma terms_length (kind : GraphRecovery.Kind) (w : PairInput) :
    (GraphRecovery.terms kind w).length=degree w+1 := by simp [GraphRecovery.terms,degree,GraphRecovery.degree]
lemma terms_get (kind : GraphRecovery.Kind) (w : PairInput) (s : ℕ) (hs : s<degree w+1) :
    (GraphRecovery.terms kind w)[s]?.getD (0,1)=GraphRecovery.term kind w ⟨s,hs⟩ := by
  exact GraphRecovery.terms_get kind w s hs
lemma terms_iterate (kind : GraphRecovery.Kind) (w : PairInput) (a : ℤ×ℤ) :
    DH.Runtime.UnaryFor.iterate (fun s a=>RationalAccumulator.step a ((GraphRecovery.terms kind w)[s]?.getD (0,1))) 0 (degree w+1) a=
      RationalAccumulator.run a (GraphRecovery.terms kind w) := by
  simpa only [terms_length] using DriverAlgebra.iterate_lookup RationalAccumulator.step (GraphRecovery.terms kind w) (0,1) a

def CellSpec (B : OracleBlock 97) (kind : GraphRecovery.Kind) (g : BitString→ℕ) (w : PairInput) (BA C : ℕ) : Prop :=
  ∀s : GraphRecovery.Index w, ∀a : ℤ×ℤ,
    ((signedBits a.1).length≤BA ∧ (signedBits a.2).length≤BA) →
    ((signedBits (GraphRecovery.term kind w s).1).length≤BA ∧ (signedBits (GraphRecovery.term kind w s).2).length≤BA) →
    ∃c,B.Executes g (state w (degree w-s.val) s.val a [] [] [])
      (state w (degree w-s.val) s.val (RationalAccumulator.step a (GraphRecovery.term kind w s)) [] [] []) c ∧ c≤C
noncomputable def probeLoop (B : OracleBlock 97) : OracleBlock 97 := DH.Runtime.UnaryFor.program 5 6 B

theorem probeLoop_executes (B : OracleBlock 97) (kind : GraphRecovery.Kind) (g : BitString→ℕ) (w : PairInput)
    (BA C : ℕ) (hSpec : CellSpec B kind g w BA C)
    (hB : RationalAccumulator.BitBound BA (0,1) (GraphRecovery.terms kind w)) :
    ∃c,(probeLoop B).Executes g (state w (degree w+1) 0 (0,1) [] [] [])
      (state w 0 (degree w+1) (RationalAccumulator.run (0,1) (GraphRecovery.terms kind w)) [] [] []) c ∧
      c ≤ (degree w+1)*(C+5)+1 ∧
      RationalAccumulator.BitBound BA (RationalAccumulator.run (0,1) (GraphRecovery.terms kind w)) [] := by
  let row := GraphRecovery.terms kind w
  let step := fun (s : ℕ) (a : ℤ×ℤ)=>RationalAccumulator.step a (row[s]?.getD (0,1))
  let st := fun (s m : ℕ) (a : ℤ×ℤ)=>state w m s a [] [] []
  let Inv := fun (s : ℕ) (a : ℤ×ℤ)=>RationalAccumulator.BitBound BA a (row.drop s)
  have hbody : ∀s m a, Inv s a → s+m+1=degree w+1 →
      ∃c,B.Executes g (st s m a) (st s m (step s a)) c ∧ c≤C ∧ Inv (s+1) (step s a) := by
    intro s m a hi he
    have hs : s<degree w+1 := by omega
    have hm : m=degree w-s := by omega
    let q : GraphRecovery.Index w := ⟨s,hs⟩
    have hget : row[s]?.getD (0,1)=GraphRecovery.term kind w q := terms_get kind w s hs
    have hr : s<row.length := by simpa only [row,terms_length] using hs
    have hi' : RationalAccumulator.BitBound BA a (row.drop s++[]) := by simpa only [List.append_nil] using hi
    obtain ⟨hitem,hnext⟩ := hi'.drop_step hr
    have hterm : (signedBits (GraphRecovery.term kind w q).1).length≤BA ∧ (signedBits (GraphRecovery.term kind w q).2).length≤BA := by rw [←hget];exact hitem
    obtain ⟨c,hc,hcb⟩ := hSpec q a hi.head hterm
    refine ⟨c,?_,hcb,?_⟩
    · simpa only [st,step,q,hm,hget] using hc
    · simpa only [Inv,step,List.append_nil] using hnext
  obtain ⟨c,hc,hcb,hinv⟩ := ComplementFor.executes (5:Fin 98) 6 B g step st Inv C (degree w+1)
    (by intros;rfl)
    (by intro s m a;exact state_update_inner w _ _ _ a [] [] [])
    (by intro s m a;change Function.update (state w m s a [] [] []) 6 (true::List.replicate s true)=_
        rw [←List.replicate_succ,state_update_s])
    hbody 0 (degree w+1) (0,1) (by simpa only [Inv,row,List.drop_zero] using hB) (by omega)
  simp only [Nat.zero_add,step,row,terms_iterate] at hc hinv
  refine ⟨c,hc,hcb,?_⟩
  have he : (GraphRecovery.terms kind w).drop (degree w+1)=[] := by rw [←terms_length kind w,List.drop_length]
  simpa only [Inv,row,he] using hinv
end HiddenCircuits.GraphReduction.Runtime.PairEval.Driver
