import HiddenCircuits.Circuit.Runtime.DeltaWordBounds
import HiddenCircuits.Circuit.Runtime.SourceInnerLoop

namespace HiddenCircuits.Circuit.Runtime.DeltaWordInterpolation
open HiddenCircuits.Complexity OracleBlock BinaryArithmetic Polynomial DeltaWordRecovery SourceInner
open HiddenCircuits.DH.Runtime

def dataState {k n : ℕ} (w : List (DeltaGate n))
    (u : ℕ) (acc : RationalAccumulator.Ratio) : Store (k+64) :=
  SourceWordCall.lifted (SourceSample.store (DeltaWordSample.canonical w u)
    {accumulator:=acc,degree:=degree w})
def state {k n : ℕ} (w : List (DeltaGate n))
    (u : ℕ) (acc : RationalAccumulator.Ratio) : Store (k+65) :=
  FramedFor.frame (dataState (k:=k) w u acc) []
noncomputable def program {k : ℕ} (W : OracleBlock k) : OracleBlock (k+65) :=
  FramedFor.program (SourceWordCall.lowEmbedding k 13) (SourceWordCall.lowEmbedding k 4) (SourceWordCall.lowEmbedding k 24)
    ((SourceWordCall.lowEmbedding k).injective.ne (by decide : (13:Fin 64)≠24)) (DeltaWordSample.program W)

lemma row_length {n : ℕ} (hn : 0<n) (w : List (DeltaGate n)) :
    (items hn w).length=degree w+1 := by
  exact items_length hn w
lemma row_get {n : ℕ} (hn : 0<n) (w : List (DeltaGate n))
    (u : Index w) :
    ((items hn w)[u.val]?.getD (0,1))=item hn w u := by
  rw [items,List.getElem?_eq_getElem (by simpa using u.isLt),Option.getD_some,List.getElem_ofFn]

set_option maxHeartbeats 1200000 in
theorem program_executes {k : ℕ} (W : OracleBlock k) (g : BitString → ℕ) (p : Polynomial ℕ)
    (hW : SourceWordCall.WordSolverSpec W g p) {n : ℕ} (hn : 0<n) (w : List (DeltaGate n))
    (acc : RationalAccumulator.Ratio) (tail : List RationalAccumulator.Ratio) (C B : ℕ)
    (hbit : RationalAccumulator.BitBound C acc (items hn w++tail))
    (hstore : ∀u : Index w,∀v : RationalAccumulator.Ratio,RationalAccumulator.Bounded C v →
      ∀j,(SourceSample.store (DeltaWordSample.canonical w u.val) {accumulator:=v,degree:=degree w} j).length≤B) :
    ∃c,(program W).Executes g (state (k:=k) w 0 acc)
      (state (k:=k) w 0 (RationalAccumulator.run acc (items hn w))) c ∧
      c≤(degree w+1)*((DeltaWordSample.time p).eval B+5)+6*degree w+12 ∧
      RationalAccumulator.BitBound C (RationalAccumulator.run acc (items hn w)) tail := by
  let xs:=items hn w
  let st:=fun i v=>dataState (k:=k) w i v
  let Inv:=fun i v=>RationalAccumulator.BitBound C v (xs.drop i++tail)
  have hbody (i : ℕ) (v : RationalAccumulator.Ratio) (hv : Inv i v) (hi : i<degree w+1) :
      ∃c,(DeltaWordSample.program W).Executes g (st i v) (st i (listStep xs i v)) c ∧
        c≤(DeltaWordSample.time p).eval B ∧ Inv (i+1) (listStep xs i v) := by
    let u : Index w:=⟨i,hi⟩
    have hil : i<xs.length := by dsimp [xs];rw [row_length];exact hi
    have hvnext:=RationalAccumulator.BitBound.drop_step hv hil
    obtain ⟨z,c,hc,hz,hb⟩:=DeltaWordSample.program_executes W g p hW hn w u v B (hstore u v hv.head)
    have he:=value_unique hn w u z hz
    subst z
    have hitem : itemOf w u (value hn w u)=xs[i]?.getD (0,1) := by
      rw [show i=u.val from rfl,show xs=items hn w from rfl,row_get]
      rfl
    rw [hitem] at hc
    exact ⟨c,hc,hb,hvnext.2⟩
  obtain ⟨c,hc,hb,hv⟩:=FramedFor.program_executes
    (SourceWordCall.lowEmbedding k 13) (SourceWordCall.lowEmbedding k 4) (SourceWordCall.lowEmbedding k 24)
    ((SourceWordCall.lowEmbedding k).injective.ne (by decide : (13:Fin 64)≠24))
    (DeltaWordSample.program W) g (listStep xs) st Inv (degree w) ((DeltaWordSample.time p).eval B)
    (by intro i v;simp [st,dataState,SourceWordCall.lifted,SourceSample.store])
    (by intro i v;simp [st,dataState,SourceWordCall.lifted,SourceSample.store,DeltaWordSample.canonical])
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
  have he : UnaryFor.iterate (listStep xs) 0 (degree w+1) acc=RationalAccumulator.run acc xs := by
    rw [←row_length hn w]
    exact iterate_all xs acc
  rw [he] at hc hv
  refine ⟨c,hc,hb,?_⟩
  simpa only [Inv,show degree w+1=xs.length from (row_length hn w).symm,List.drop_length,List.nil_append] using hv
noncomputable def loopTime (p : Polynomial ℕ) : Polynomial ℕ :=
  (2*X+1)*((DeltaWordSample.time p).comp DeltaWordBounds.storageSize+5)+12*X+12
noncomputable def inputBound : Polynomial ℕ := X+DeltaWordBounds.prefixBitSize
noncomputable def time (p : Polynomial ℕ) : Polynomial ℕ := (loopTime p).comp inputBound
noncomputable def result {n : ℕ} (hn : 0<n) (w : List (DeltaGate n)) : RationalAccumulator.Ratio :=
  RationalAccumulator.run (0,1) (items hn w)
lemma result_correct {n : ℕ} (hn : 0<n) (w : List (DeltaGate n)) :
    (result hn w).2≠0 ∧ RationalAccumulator.value (result hn w)=deltaCircuitMatrix w (zeroBits n) (zeroBits n) := by
  refine ⟨RationalAccumulator.run_nonzero _ _ (by decide) (items_nonzero hn w),?_⟩
  rw [result,RationalAccumulator.run_value _ _ (by decide) (items_nonzero hn w),items_value]
  simp [RationalAccumulator.value]
theorem program_executes_polynomial {k : ℕ} (W : OracleBlock k) (g : BitString→ℕ) (p : Polynomial ℕ)
    (hW : SourceWordCall.WordSolverSpec W g p) {n : ℕ} (hn : 0<n) (w : List (DeltaGate n)) :
    ∃c,(program W).Executes g (state (k:=k) w 0 (0,1)) (state (k:=k) w 0 (result hn w)) c ∧
      c≤(time p).eval (DeltaWordEmitter.circuitBits n w).length := by
  let L:=(DeltaWordEmitter.circuitBits n w).length
  let C:=DeltaWordBounds.prefixBitSize.eval L
  obtain ⟨c,hc,hb,hv⟩:=program_executes W g p hW hn w (0,1) [] C
    (DeltaWordBounds.storageSize.eval (L+C)) (by simpa using DeltaWordBounds.bitBound hn w)
    (fun u v hv=>DeltaWordBounds.state_bound w u C v hv)
  refine ⟨c,hc,?_⟩
  have hd:degree w≤2*(L+C):= (DeltaWordBounds.degree_bound w).trans (by omega)
  have hm:=Nat.mul_le_mul_right ((DeltaWordSample.time p).eval (DeltaWordBounds.storageSize.eval (L+C))+5)
    (Nat.add_le_add_right hd 1)
  simp only [time,loopTime,inputBound,eval_add,eval_mul,eval_comp,eval_X,eval_ofNat,eval_one]
  change c≤(2*(L+C)+1)*((DeltaWordSample.time p).eval (DeltaWordBounds.storageSize.eval (L+C))+5)+12*(L+C)+12
  omega
end HiddenCircuits.Circuit.Runtime.DeltaWordInterpolation
