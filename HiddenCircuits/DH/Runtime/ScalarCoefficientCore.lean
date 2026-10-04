import HiddenCircuits.DH.Runtime.FactorialInto
import HiddenCircuits.DH.Runtime.CrossTerm
import HiddenCircuits.Complexity.CNFCloneEmitter.UnarySplit

/-! Public indices and cached coefficient words are
read-only. Five real factorial producers populate the straight-line arithmetic
registers; the two unary differences are computed by actual consuming loops. -/
namespace HiddenCircuits.DH.Runtime.ScalarCoefficient
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic
open Complexity.BinaryArithmetic.RegisterMachine
open Polynomial
set_option maxHeartbeats 2000000

def state (i j r : ℕ) (A B output : BitString) (d e : ℕ) (R : Fin 7→ BitString) : Store 25 := fun q=>
  if q.val=0 then List.replicate i true else if q.val=1 then List.replicate j true
  else if q.val=2 then List.replicate r true else if q.val=3 then A else if q.val=4 then B
  else if q.val=5 then output else if q.val=6 then List.replicate d true
  else if q.val=7 then List.replicate e true else
  if h : 17≤ q.val ∧ q.val<24 then R ⟨q.val-17,by omega⟩ else []
def store (i j r A B : ℕ) (output : BitString) : Store 25 :=
  state i j r (signedBits (A:ℤ)) (signedBits (B:ℤ)) output 0 0 (fun _=>[])
def fport (v : Fin 7) : Fin 26 := ⟨17+v.val,by omega⟩
def factorialMap (src : Fin 8) (dst : Fin 7) : Fin 9↪Fin 26 where
  toFun q := ⟨if q.val=0 then src.val else if q.val=1 then 17+dst.val else q.val+6,by split_ifs <;> omega⟩
  inj' := by
    intro q z h
    apply Fin.ext
    have hh:=congrArg Fin.val h
    change (if q.val=0 then src.val else if q.val=1 then 17+dst.val else q.val+6)=
      (if z.val=0 then src.val else if z.val=1 then 17+dst.val else z.val+6) at hh
    split_ifs at hh <;> omega
noncomputable def factorial (src : Fin 8) (dst : Fin 7) : OracleBlock 25 := FactorialInto.on (factorialMap src dst)

lemma state_fport (i j r : ℕ) (A B output : BitString) (d e : ℕ) (R : Fin 7→ BitString) (v : Fin 7) :
    state i j r A B output d e R (fport v)=R v := by
  simp [state,fport,show ¬17+v.val=0 by omega,show ¬17+v.val=1 by omega,
    show ¬17+v.val=2 by omega,show ¬17+v.val=3 by omega,show ¬17+v.val=4 by omega,
    show ¬17+v.val=5 by omega,show ¬17+v.val=6 by omega,show ¬17+v.val=7 by omega,
    show 17+v.val<24 by omega]

lemma state_update_register (i j r : ℕ) (A B output : BitString) (d e : ℕ) (R : Fin 7→ BitString)
    (dst : Fin 7) (word : BitString) :
    Function.update (state i j r A B output d e R) (fport dst) word=
      state i j r A B output d e (Function.update R dst word) := by
  funext q
  by_cases h : q=fport dst
  · subst q; simp [state_fport]
  · rw [Function.update_of_ne h]
    unfold state
    split_ifs with h0 h1 h2 h3 h4 h5 h6 h7 hr <;> try rfl
    apply (Function.update_of_ne (show (⟨q.val-17,by omega⟩:Fin 7)≠dst from by
      intro he;apply h;apply Fin.ext;have := congrArg Fin.val he;change q.val=17+dst.val;dsimp at this;omega) _ _).symm

lemma factorial_executes (g : BitString→ ℕ) (i j r : ℕ) (A B output : BitString)
    (d e : ℕ) (R : Fin 7→ BitString) (src : Fin 8) (dst : Fin 7) (x : ℕ)
    (hx : state i j r A B output d e R ⟨src.val,by omega⟩=List.replicate x true)
    (hz : R dst=[]) :
    ∃t,(factorial src dst).Executes g (state i j r A B output d e R)
      (state i j r A B output d e (Function.update R dst (signedBits (x.factorial:ℤ)))) t ∧ t≤ FactorialInto.time.eval x := by
  obtain ⟨t,ht,hb⟩ := FactorialInto.on_executes (factorialMap src dst) g
    (state i j r A B output d e R) (List.replicate x true) (by
      funext q; fin_cases q
      · exact hx
      · simpa only [Function.comp_def,factorialMap,↓reduceIte] using (state_fport i j r A B output d e R dst).trans hz
      all_goals rfl)
  refine ⟨t,?_,by simpa using hb⟩
  change (factorial src dst).Executes g _ (Function.update _ (fport dst) (signedBits ((List.replicate x true).length.factorial:ℤ))) t at ht
  simpa only [List.length_replicate,state_update_register] using ht

def splitMap (dst : Fin 2) : Fin 3↪Fin 26 where
  toFun q:=if q.val=0 then ⟨6+dst.val,by omega⟩ else if q.val=1 then 24 else 25
  inj':=by fin_cases dst <;> decide +kernel
noncomputable def difference (src : Fin 2) : OracleBlock 25 :=
  seq (copyOn ⟨src.val,by omega⟩ ⟨6+src.val,by omega⟩ 24 (by fin_cases src <;> decide)
    (by fin_cases src <;> decide) (by fin_cases src <;> decide))
  (seq (copyOn 2 24 25 (by decide) (by decide) (by decide))
    (seq (CNFCloneEmitter.UnarySplit.on (splitMap src)) (clear 25)))

lemma difference_executes (g : BitString→ ℕ) (i j r : ℕ) (A B output : BitString)
    (d e : ℕ) (R : Fin 7→ BitString) (src : Fin 2)
    (hz : if src.val=0 then d=0 else e=0) :
    ∃t,(difference src).Executes g (state i j r A B output d e R)
      (state i j r A B output (if src.val=0 then i-r else d) (if src.val=0 then e else j-r) R) t ∧
      t≤ 5*(i+j)+14*r+20 := by
  let s:=state i j r A B output d e R
  let source:Fin 26:=⟨src.val,by omega⟩
  let target:Fin 26:=⟨6+src.val,by omega⟩
  let x:=if src.val=0 then i else j
  have hx:s source=List.replicate x true:=by fin_cases src <;> rfl
  have hz':s target=[]:=by fin_cases src <;> simp_all [s,target,state]
  have hc:=copyOn_executes g source target 24 (by intro h;have:=congrArg Fin.val h;dsimp [source,target] at this;omega)
    (by intro h;have:=congrArg Fin.val h;dsimp [source] at this;omega)
    (by intro h;have:=congrArg Fin.val h;dsimp [target] at this;omega) s rfl
  rw [hx,hz',List.append_nil,List.length_replicate] at hc
  let s1:=Function.update s target (List.replicate x true)
  have hc2:=copyOn_executes g (2:Fin 26) 24 25 (by decide) (by decide) (by decide) s1 (by
    dsimp [s1,target,s,state];rw [Function.update_of_ne (by intro h;have:=congrArg Fin.val h;dsimp at this;omega)];rfl)
  have hs1:s1 2=List.replicate r true:=by dsimp [s1,target];rw [Function.update_of_ne (by intro h;have:=congrArg Fin.val h;dsimp at this;omega)];rfl
  have hs24:s1 24=[]:=by dsimp [s1,target];rw [Function.update_of_ne (by intro h;have:=congrArg Fin.val h;dsimp at this;omega)];rfl
  rw [hs1,hs24,List.append_nil,List.length_replicate] at hc2
  let s2:=Function.update s1 24 (List.replicate r true)
  obtain ⟨c,hs,hcb⟩:=CNFCloneEmitter.UnarySplit.on_executes (splitMap src) g s2 x r (by
    funext q;fin_cases src <;> fin_cases q <;> rfl)
  let s3:=Function.update (Function.update (Function.update s2 ((splitMap src) 0) (List.replicate (x-r) true)) ((splitMap src) 1) []) ((splitMap src) 2) [decide (x<r)]
  have hd:=clear_executes g (25:Fin 26) s3
  have hl:(s3 25).length=1:=by simp [s3,splitMap]
  rw [hl] at hd
  have hall:=seq_executes _ _ g hc (seq_executes _ _ g hc2 (seq_executes _ _ g hs hd))
  refine ⟨5*x+2+(5*r+2+(c+2+2)+2)+2,?_,?_⟩
  · convert hall using 1
    funext q;fin_cases src <;> fin_cases q <;> simp_all [s3,s2,s1,s,source,target,x,splitMap,state]
  · dsimp [x];split_ifs <;> omega

lemma difference_queryFree (src : Fin 2) : (difference src).QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (CNFCloneEmitter.UnarySplit.on_queryFree _) (clear_queryFree _)))

end HiddenCircuits.DH.Runtime.ScalarCoefficient
