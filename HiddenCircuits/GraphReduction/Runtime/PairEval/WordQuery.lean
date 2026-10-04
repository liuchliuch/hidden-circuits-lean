import HiddenCircuits.Complexity.PairEncoding
import HiddenCircuits.PairedInterpolation
import HiddenCircuits.Complexity.PairSerialization
import HiddenCircuits.GraphReduction.Runtime.WordGraph.WordSamplePolynomial
import HiddenCircuits.GraphReduction.Runtime.WordGraph.QueryAnswer

/-! Physical serialization of the sampled pair instance, followed by exactly
one natural-valued oracle instruction. The input, indices and all scratch ports
have the same clean contract as the established WordGraph query cells. -/
namespace HiddenCircuits.GraphReduction.Runtime.PairEval.WordQuery
open Complexity OracleBlock BinaryArithmetic Polynomial WordGraph
set_option maxHeartbeats 1000000

def sampleInput (w : WordInstance) (hw : w.word≠[]) (t : ℕ) : PairInput :=
  ⟨w.particles,w.positive,w.source,w.target,sampleWord w.word t,pairedQuery_nonempty w.word hw t⟩
def queryBits (w : WordInstance) (t : ℕ) : BitString :=
  pairBits (List.replicate w.particles true)
    (encodeBitList (stateBits w.source::stateBits w.target::(sampleWord w.word t).map pairAtom))
@[simp] lemma queryBits_eq (w : WordInstance) (hw : w.word≠[]) (t : ℕ) :
    queryBits w t=pairInputBits (sampleInput w hw t) := rfl

def packEmbedding (src : Fin 4) : Fin 3 ↪ Fin 18 where
  toFun i := if i.val=0 then 12 else if i.val=1 then ⟨src.val,by omega⟩ else 7
  inj' := by intro i j h;fin_cases src <;> fin_cases i <;> fin_cases j <;> simp_all
noncomputable def pack (src : Fin 4) : OracleBlock 17 := PairSerialization.on (packEmbedding src)
noncomputable def packHead (src : Fin 4) : OracleBlock 17 := seq (pack src) (push 12 true)
def packed (s : Store 17) (src : Fin 4) (xs ys : BitString) : Store 17 :=
  Function.update (Function.update s ⟨src.val,by omega⟩ []) 12 (pairBits xs ys)
def headed (s : Store 17) (src : Fin 4) (xs ys : BitString) : Store 17 :=
  Function.update (Function.update s ⟨src.val,by omega⟩ []) 12 (true::pairBits xs ys)

lemma pack_executes (g : BitString→ℕ) (src : Fin 4) (s : Store 17) (xs ys : BitString)
    (hs : s ⟨src.val,by omega⟩=xs) (hy : s 12=ys) (hz : s 7=[]) :
    (pack src).Executes g s (packed s src xs ys) (10*xs.length+9) := by
  apply PairSerialization.on_executes _ g s xs ys
  funext i;fin_cases i <;> simp [packEmbedding,PairSerialization.state,Function.comp_def,hs,hy,hz]
lemma packHead_executes (g : BitString→ℕ) (src : Fin 4) (s : Store 17) (xs ys : BitString)
    (hs : s ⟨src.val,by omega⟩=xs) (hy : s 12=ys) (hz : s 7=[]) :
    (packHead src).Executes g s (headed s src xs ys) (10*xs.length+12) := by
  have h:=pack_executes g src s xs ys hs hy hz
  have hp : (push (12:Fin 18) true).Executes g (packed s src xs ys) (headed s src xs ys) 1 := by
    convert push_executes g (12:Fin 18) true (packed s src xs ys) using 1
    simp [packed,headed]
  convert seq_executes _ _ g h hp using 1 <;> omega

noncomputable def serialize : OracleBlock 17 := seq (packHead 3) (seq (packHead 2) (pack 1))
def serialized (w : WordInstance) (t : ℕ) : Store 17 :=
  packed (headed (headed (WordSample.output w t) 3 (stateBits w.target) (pairStream (sampleWord w.word t)))
    2 (stateBits w.source) (true::pairBits (stateBits w.target) (pairStream (sampleWord w.word t))))
    1 (List.replicate w.particles true)
      (true::pairBits (stateBits w.source) (true::pairBits (stateBits w.target) (pairStream (sampleWord w.word t))))
lemma serialized_query (w : WordInstance) (t : ℕ) : serialized w t 12=queryBits w t := rfl
lemma serialize_executes (g : BitString→ℕ) (w : WordInstance) (t : ℕ) :
    serialize.Executes g (WordSample.output w t) (serialized w t) (50*w.particles+37) := by
  have h1:=packHead_executes g 3 (WordSample.output w t) (stateBits w.target) (pairStream (sampleWord w.word t)) rfl rfl rfl
  have h2:=packHead_executes g 2 (headed (WordSample.output w t) 3 (stateBits w.target) (pairStream (sampleWord w.word t)))
    (stateBits w.source) (true::pairBits (stateBits w.target) (pairStream (sampleWord w.word t))) rfl rfl rfl
  have h3:=pack_executes g 1 (headed (headed (WordSample.output w t) 3 (stateBits w.target) (pairStream (sampleWord w.word t)))
    2 (stateBits w.source) (true::pairBits (stateBits w.target) (pairStream (sampleWord w.word t))))
    (List.replicate w.particles true)
    (true::pairBits (stateBits w.source) (true::pairBits (stateBits w.target) (pairStream (sampleWord w.word t)))) rfl rfl rfl
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 h3) using 1
  simp only [stateBits_length,List.length_replicate]
  omega
noncomputable def sample : OracleBlock 17 := seq WordSample.program serialize
noncomputable def sampleTime : Polynomial ℕ := WordSample.time+50*X+39
lemma sample_executes (g : BitString→ℕ) (w : WordInstance) (t : ℕ) :
    ∃c,sample.Executes g (WordParser.store (wordBits w) [] [] [] [] [] (List.replicate t true))
      (serialized w t) c ∧ c≤sampleTime.eval ((wordBits w).length+t) := by
  obtain ⟨c,hc,hb⟩:=WordSample.program_polynomial g w t
  refine ⟨_,seq_executes _ _ g hc (serialize_executes g w t),?_⟩
  have hin:=wordBits_length_lower w
  simp only [sampleTime,eval_add,eval_mul,eval_ofNat,eval_X]
  omega

def embedding : Fin 18 ↪ Fin 86 where
  toFun i:=⟨i.val+4,by omega⟩
  inj' := by intro i j h;apply Fin.ext;have := congrArg Fin.val h;dsimp only at this;omega
def bankState (w : WordInstance) (t s : ℕ) (low : Store 17) : Store 85 := fun i =>
  if h:i.val<4 then QueryAnswer.store (wordBits w) t s [] i
  else if h:i.val<22 then low ⟨i.val-4,by omega⟩ else []
noncomputable def before : OracleBlock 85 := seq (copyOn 0 4 22 (by decide) (by decide) (by decide))
  (seq (copyOn 1 10 22 (by decide) (by decide) (by decide)) (rename sample embedding))
noncomputable def beforeTime : Polynomial ℕ := sampleTime+5*X+8
lemma before_executes (g : BitString→ℕ) (w : WordInstance) (t s : ℕ) :
    ∃c,before.Executes g (QueryAnswer.store (wordBits w) t s []) (bankState w t s (serialized w t)) c ∧
      c≤beforeTime.eval ((wordBits w).length+t+s) := by
  let a:=Function.update (QueryAnswer.store (wordBits w) t s []) (4:Fin 86) (wordBits w)
  let b:=Function.update a (10:Fin 86) (List.replicate t true)
  have h1:(copyOn (0:Fin 86) 4 22 (by decide) (by decide) (by decide)).Executes g
      (QueryAnswer.store (wordBits w) t s []) a (5*(wordBits w).length+2) := by
    simpa [a,QueryAnswer.store] using copyOn_executes g (0:Fin 86) 4 22 (by decide) (by decide) (by decide) (QueryAnswer.store (wordBits w) t s []) rfl
  have h2:(copyOn (1:Fin 86) 10 22 (by decide) (by decide) (by decide)).Executes g a b (5*t+2) := by
    simpa [a,b,QueryAnswer.store] using copyOn_executes g (1:Fin 86) 10 22 (by decide) (by decide) (by decide) a rfl
  obtain ⟨c,hc,hb⟩:=sample_executes g w t
  have h3:(rename sample embedding).Executes g b (bankState w t s (serialized w t)) c := by
    apply rename_executes_to sample embedding g hc
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi
      have hr:¬(4 ≤ i.val ∧ i.val<22) := by
        intro h;exact hi ⟨i.val-4,by omega⟩ (Fin.ext (by simp [embedding];omega))
      have h4:i≠4:=by intro h;subst i;norm_num at hr
      have h10:i≠10:=by intro h;subst i;norm_num at hr
      simp only [b,a,Function.update_of_ne h4,Function.update_of_ne h10,bankState]
      split_ifs with h h
      · rfl
      · omega
      · simp only [QueryAnswer.store]
        split_ifs <;> simp_all <;> omega
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 h3),?_⟩
  have hm:=polynomial_nat_eval_mono sampleTime (show (wordBits w).length+t≤(wordBits w).length+t+s by omega)
  simp only [beforeTime,eval_add,eval_mul,eval_ofNat,eval_X]
  dsimp only at hm
  omega

noncomputable def program : OracleBlock 85 := seq before (seq (query 16 3)
  (seq (clearList QueryAnswer.cleanupPorts) (push 3 false)))
noncomputable def time : Polynomial ℕ := 1000*(beforeTime+X+2)

lemma program_polynomial (g : BitString→ℕ) (w : WordInstance) (t s : ℕ) :
    ∃c,program.Executes g (QueryAnswer.store (wordBits w) t s [])
      (QueryAnswer.store (wordBits w) t s (signedBits (g (queryBits w t):ℤ))) c ∧
      c≤time.eval ((wordBits w).length+t+s+(signedBits (g (queryBits w t):ℤ)).length) := by
  let N:=(wordBits w).length+t+s
  let finish:=bankState w t s (serialized w t)
  let answer:=Computability.encodeNat (g (queryBits w t))
  obtain ⟨a,ha,hab⟩:=before_executes g w t s
  have hin:∀i,(QueryAnswer.store (wordBits w) t s [] i).length≤N := by
    intro i;unfold QueryAnswer.store;split_ifs <;> (try simp only [List.length_replicate,List.length_nil]) <;> dsimp [N] <;> omega
  have hs:∀i,(finish i).length≤N+a:=ha.stack_bound hin
  have hq:(query (16:Fin 86) 3).Executes g finish (Function.update finish 3 answer)
      (1+(queryBits w t).length+answer.length):=query_executes g 16 3 finish
  obtain ⟨b,hb,hbb⟩:=clearList_executes_local g QueryAnswer.cleanupPorts (Function.update finish 3 answer) (N+a) (by
    intro i hi
    have hv:4 ≤ i.val:=by simpa [QueryAnswer.cleanupPorts] using hi
    have h3:i≠3:=by intro h;subst i;norm_num at hv
    simpa [Function.update_of_ne h3] using hs i)
  have he:eraseStore QueryAnswer.cleanupPorts (Function.update finish 3 answer)=QueryAnswer.store (wordBits w) t s answer := by
    funext i;fin_cases i <;> simp [eraseStore,QueryAnswer.cleanupPorts,finish,bankState,QueryAnswer.store]
  rw [he] at hb
  have hp:(push (3:Fin 86) false).Executes g (QueryAnswer.store (wordBits w) t s answer)
      (QueryAnswer.store (wordBits w) t s (signedBits (g (queryBits w t):ℤ))) 1 := by
    convert push_executes g (3:Fin 86) false (QueryAnswer.store (wordBits w) t s answer) using 1
    funext i;fin_cases i <;> simp [QueryAnswer.store,answer,signedBits,negative]
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hq (seq_executes _ _ g hb hp)),?_⟩
  have hlen:=hs 16
  change (queryBits w t).length≤N+a at hlen
  have hl:QueryAnswer.cleanupPorts.length≤86:=(List.length_filter_le _ _).trans (by simp)
  have hb':=hbb.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hl) 1)
  have hm:=polynomial_nat_eval_mono beforeTime (show N≤N+(signedBits (g (queryBits w t):ℤ)).length by omega)
  have hans:answer.length≤(signedBits (g (queryBits w t):ℤ)).length := by simp [answer,signedBits]
  dsimp only at hm
  simp only [time,eval_mul,eval_add,eval_X,eval_ofNat]
  change a+(1+(queryBits w t).length+answer.length+(b+1+2)+2)+2≤_
  change a≤beforeTime.eval N at hab
  change _≤1000*(beforeTime.eval (N+(signedBits (g (queryBits w t):ℤ)).length)+(N+(signedBits (g (queryBits w t):ℤ)).length)+2)
  omega
end HiddenCircuits.GraphReduction.Runtime.PairEval.WordQuery
