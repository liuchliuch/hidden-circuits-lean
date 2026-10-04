import HiddenCircuits.Circuit.Runtime.SourceSampleProgram
import HiddenCircuits.Circuit.Runtime.SourceSampleIntegers
import HiddenCircuits.Circuit.Runtime.FramedFor

/-! Actual unary geometric-node iteration with the global
integer prefix bound carried through the literal remaining item list. -/
namespace HiddenCircuits.Circuit.Runtime.SourceInner
open HiddenCircuits.Complexity OracleBlock BinaryArithmetic Polynomial SourceQueryRecovery
open HiddenCircuits.DH.Runtime

noncomputable def listStep (xs : List RationalAccumulator.Ratio) (i : ℕ) (a : RationalAccumulator.Ratio) : RationalAccumulator.Ratio :=
  RationalAccumulator.step a (xs[i]?.getD (0,1))

lemma iterate_list (xs : List RationalAccumulator.Ratio) (i m : ℕ) (a : RationalAccumulator.Ratio) (h : i+m≤xs.length) :
    UnaryFor.iterate (listStep xs) i m a=RationalAccumulator.run a ((xs.drop i).take m) := by
  induction m generalizing i a with
  | zero => simp [UnaryFor.iterate,RationalAccumulator.run]
  | succ m ih =>
    have hi : i<xs.length := by omega
    rw [UnaryFor.iterate,ih (i+1) _ (by omega),List.drop_eq_getElem_cons hi,List.take_succ_cons,RationalAccumulator.run_cons]
    simp only [listStep,List.getElem?_eq_getElem hi,Option.getD_some]
lemma iterate_all (xs : List RationalAccumulator.Ratio) (a : RationalAccumulator.Ratio) :
    UnaryFor.iterate (listStep xs) 0 xs.length a=RationalAccumulator.run a xs := by
  simpa using iterate_list xs 0 xs.length a (by omega)

def dataState {k n : ℕ} (w : List (ConstraintGate n)) (a : ℕ) (r : FirstIndex w) (s : SecondIndex w)
    (u : ℕ) (acc : RationalAccumulator.Ratio) : Store (k+64) :=
  SourceWordCall.lifted (SourceSample.store (SourceSample.canonical w a r.val s.val u)
    {accumulator:=acc,degree:=degree w r.val s.val})
def state {k n : ℕ} (w : List (ConstraintGate n)) (a : ℕ) (r : FirstIndex w) (s : SecondIndex w)
    (u : ℕ) (acc : RationalAccumulator.Ratio) : Store (k+65) :=
  FramedFor.frame (dataState (k:=k) w a r s u acc) []
noncomputable def program {k : ℕ} (W : OracleBlock k) : OracleBlock (k+65) :=
  FramedFor.program (SourceWordCall.lowEmbedding k 13) (SourceWordCall.lowEmbedding k 4) (SourceWordCall.lowEmbedding k 24)
    ((SourceWordCall.lowEmbedding k).injective.ne (by decide : (13:Fin 64)≠24)) (SourceSample.program W)

lemma row_length {n : ℕ} (hn : 0<n) (a : ℕ) (w : List (ConstraintGate n)) (r : FirstIndex w) (s : SecondIndex w) :
    (SourceSampleIntegers.rowItems hn a w r s).length=degree w r.val s.val+1 := by
  simp [SourceSampleIntegers.rowItems,ThirdIndex,SourceQueryRecovery.degree]
lemma row_get {n : ℕ} (hn : 0<n) (a : ℕ) (w : List (ConstraintGate n)) (r : FirstIndex w) (s : SecondIndex w)
    (u : ThirdIndex w r s) :
    ((SourceSampleIntegers.rowItems hn a w r s)[u.val]?.getD (0,1))=SourceSampleIntegers.item hn a w r s u := by
  rw [SourceSampleIntegers.rowItems,List.getElem?_eq_getElem (by simpa using u.isLt),Option.getD_some,List.getElem_ofFn]

set_option maxHeartbeats 1200000 in
theorem program_executes {k : ℕ} (W : OracleBlock k) (g : BitString → ℕ) (p : Polynomial ℕ)
    (hW : SourceWordCall.WordSolverSpec W g p) {n : ℕ} (hn : 0<n) (a : ℕ) (w : List (ConstraintGate n))
    (r : FirstIndex w) (s : SecondIndex w) (acc : RationalAccumulator.Ratio) (tail : List RationalAccumulator.Ratio) (C B : ℕ)
    (hbit : RationalAccumulator.BitBound C acc (SourceSampleIntegers.rowItems hn a w r s++tail))
    (hstore : ∀u : ThirdIndex w r s,∀v : RationalAccumulator.Ratio,RationalAccumulator.Bounded C v →
      ∀j,(SourceSample.store (SourceSample.canonical w a r.val s.val u.val) {accumulator:=v,degree:=degree w r.val s.val} j).length≤B) :
    ∃c,(program W).Executes g (state (k:=k) w a r s 0 acc)
      (state (k:=k) w a r s 0 (RationalAccumulator.run acc (SourceSampleIntegers.rowItems hn a w r s))) c ∧
      c≤(degree w r.val s.val+1)*((SourceSample.time p).eval B+5)+6*degree w r.val s.val+12 ∧
      RationalAccumulator.BitBound C (RationalAccumulator.run acc (SourceSampleIntegers.rowItems hn a w r s)) tail := by
  let xs:=SourceSampleIntegers.rowItems hn a w r s
  let st:=fun i v=>dataState (k:=k) w a r s i v
  let Inv:=fun i v=>RationalAccumulator.BitBound C v (xs.drop i++tail)
  have hbody (i : ℕ) (v : RationalAccumulator.Ratio) (hv : Inv i v) (hi : i<degree w r.val s.val+1) :
      ∃c,(SourceSample.program W).Executes g (st i v) (st i (listStep xs i v)) c ∧
        c≤(SourceSample.time p).eval B ∧ Inv (i+1) (listStep xs i v) := by
    let u : ThirdIndex w r s:=⟨i,hi⟩
    have hil : i<xs.length := by dsimp [xs];rw [row_length];exact hi
    have hvnext:=RationalAccumulator.BitBound.drop_step hv hil
    obtain ⟨z,c,hc,hz,hb⟩:=SourceSample.program_executes W g p hW hn w a r s u v B (hstore u v hv.head)
    have he:=SourceSampleIntegers.value_unique hn w r s u z hz
    subst z
    have hitem : SourceSample.item a w r s u (SourceSampleIntegers.value hn w r s u)=xs[i]?.getD (0,1) := by
      rw [show i=u.val from rfl,show xs=SourceSampleIntegers.rowItems hn a w r s from rfl,row_get]
      rfl
    rw [hitem] at hc
    exact ⟨c,hc,hb,hvnext.2⟩
  obtain ⟨c,hc,hb,hv⟩:=FramedFor.program_executes
    (SourceWordCall.lowEmbedding k 13) (SourceWordCall.lowEmbedding k 4) (SourceWordCall.lowEmbedding k 24)
    ((SourceWordCall.lowEmbedding k).injective.ne (by decide : (13:Fin 64)≠24))
    (SourceSample.program W) g (listStep xs) st Inv (degree w r.val s.val) ((SourceSample.time p).eval B)
    (by intro i v;simp [st,dataState,SourceWordCall.lifted,SourceSample.store])
    (by intro i v;simp [st,dataState,SourceWordCall.lifted,SourceSample.store,SourceSample.canonical])
    (by intro i v;simp [st,dataState,SourceWordCall.lifted,SourceSample.store])
    (by intro i v
        dsimp only [st,dataState,SourceWordCall.lifted]
        change Function.update (SourceWordCall.store _ (fun _=>[])) (SourceWordCall.lowEmbedding k 4) _=_
        rw [SourceWordCall.store_low]
        change Function.update (SourceWordCall.store _ (fun _=>[])) (SourceWordCall.lowEmbedding k 4) (List.replicate (i+1) true)=_
        rw [SourceWordCall.update_low,SourceSample.update_u]
        rfl)
    (by intro v
        change Function.update (SourceWordCall.store _ (fun _=>[])) (SourceWordCall.lowEmbedding k 4) (List.replicate 0 true)=_
        rw [SourceWordCall.update_low,SourceSample.update_u]
        rfl)
    hbody acc (by simpa only [Inv,List.drop_zero] using hbit)
  have he : UnaryFor.iterate (listStep xs) 0 (degree w r.val s.val+1) acc=RationalAccumulator.run acc xs := by
    rw [←row_length hn a w r s]
    exact iterate_all xs acc
  rw [he] at hc hv
  refine ⟨c,hc,hb,?_⟩
  simpa only [Inv,show degree w r.val s.val+1=xs.length from (row_length hn a w r s).symm,List.drop_length,List.nil_append] using hv
end HiddenCircuits.Circuit.Runtime.SourceInner
