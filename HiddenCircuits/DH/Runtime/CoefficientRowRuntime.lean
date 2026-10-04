import HiddenCircuits.DH.Runtime.CoefficientEntry
import HiddenCircuits.DH.Runtime.CoefficientRowModel
import HiddenCircuits.DH.Runtime.WordArrayInitialize

/-! A real fourth unary loop writes every coefficient
into a dynamically allocated canonical word array; there is no supplied table. -/
namespace HiddenCircuits.DH.Runtime.CoefficientRowRuntime
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic PruningModel CoefficientRow
open UniformCoefficientModel Polynomial
set_option maxHeartbeats 2200000

def state (n a b : ℕ) (left right : List ℕ) (k clock : ℕ) (out word : BitString) : Store 38:=fun q=>
  if q.val=0 then List.replicate n true else if q.val=1 then List.replicate a true
  else if q.val=2 then List.replicate b true else if q.val=3 then rowBits left else if q.val=4 then rowBits right
  else if q.val=5 then out else if q.val=6 then List.replicate k true else if q.val=7 then word
  else if q.val=8 then List.replicate clock true else []
def prefixState (n : ℕ) (kind : Kind) (a b : ℕ) (left right : List ℕ) (k clock : ℕ) : Store 38:=
  state n a b left right k clock (rowBits (rowPrefix n kind a b left right k)) []
def store (n a b : ℕ) (left right : List ℕ) (out : BitString) : Store 38:=state n a b left right 0 0 out []
def entryMap : Fin 36↪Fin 39 where
  toFun q:=⟨if q.val=0 then 1 else if q.val=1 then 2 else if q.val=2 then 6 else if q.val=3 then 3
    else if q.val=4 then 4 else if q.val=5 then 7 else q.val+3,by split_ifs <;> omega⟩
  inj':=by
    intro q z h;apply Fin.ext;have hh:=congrArg Fin.val h
    simp only at hh
    split_ifs at hh <;> omega
-- Fixed literal maps, checked by the kernel rather than by execution reflection.
def updateMap : Fin 8↪Fin 39:=⟨fun q=>![5,6,7,9,10,11,12,13] q,by decide +kernel⟩
def initMap : Fin 8↪Fin 39:=⟨fun q=>![5,8,7,9,10,11,12,13] q,by decide +kernel⟩
noncomputable def body (kind : Kind) : OracleBlock 38:=seq (CoefficientEntry.on entryMap kind)
  (seq (WordArray.updateOn updateMap) (seq (clear 7) (push 6 true)))
noncomputable def loop (kind : Kind) : OracleBlock 38:=whilePop 8 (body kind) (body kind)
noncomputable def bodyTime : Polynomial ℕ:=CoefficientEntry.time+100000*(X+1)^6
noncomputable def time : Polynomial ℕ:=(X+1)*(bodyTime+2)+1000*(X+1)^2
noncomputable def setup : OracleBlock 38:=seq (copyOn 0 8 9 (by decide) (by decide) (by decide))
  (seq (push 8 true) (seq (push 7 false) (seq (WordArray.initializeOn initMap) (clear 7))))
noncomputable def program (kind : Kind) : OracleBlock 38:=seq setup (seq (loop kind) (clear 6))

lemma words_step (n : ℕ) (kind : Kind) (a b : ℕ) (left right : List ℕ) (k : ℕ) (hk:k≤ n) :
    encodeBitList ((rowWords (rowPrefix n kind a b left right k)).set k (signedBits (entry kind a b left right k:ℕ)))=
      rowBits (rowPrefix n kind a b left right (k+1)):=by
  unfold rowBits rowWords
  rw [←List.map_set,rowPrefix_step n kind a b left right k hk]

lemma body_executes (g : BitString→ ℕ) (n : ℕ) (kind : Kind) (a b : ℕ) (left right : List ℕ)
    (ha:a≤ n) (hb:b≤ n) (hl:left.length=n+1) (hr:right.length=n+1) (k clock : ℕ) (hk:k≤ n) :
    ∃t,(body kind).Executes g (prefixState n kind a b left right k clock)
      (prefixState n kind a b left right (k+1) clock) t ∧t≤ bodyTime.eval (inputSize n left right) := by
  let value:=entry kind a b left right k
  let word:=signedBits (value:ℕ)
  let s1:=state n a b left right k clock (rowBits (rowPrefix n kind a b left right k)) word
  let s2:=state n a b left right k clock (rowBits (rowPrefix n kind a b left right (k+1))) word
  let s3:=state n a b left right k clock (rowBits (rowPrefix n kind a b left right (k+1))) []
  obtain ⟨a',ha',hba⟩:=CoefficientEntry.on_executes entryMap g (prefixState n kind a b left right k clock)
    n kind left right a b k ha hb hk hl hr (by funext q;fin_cases q <;> rfl)
  have he:(CoefficientEntry.on entryMap kind).Executes g (prefixState n kind a b left right k clock) s1 a':=by
    convert ha' using 1;funext q;fin_cases q <;> rfl
  obtain ⟨b',hb',hbb⟩:=WordArray.updateOn_executes updateMap g s1 (rowWords (rowPrefix n kind a b left right k)) k word
    (by funext q;fin_cases q <;> rfl)
  have hu:(WordArray.updateOn updateMap).Executes g s1 s2 b':=by
    rw [show word=signedBits (entry kind a b left right k:ℕ) from rfl,words_step n kind a b left right k hk] at hb'
    convert hb' using 1;funext q;fin_cases q <;> rfl
  have hc:(clear (7:Fin 39)).Executes g s2 s3 (word.length+1):=by
    convert clear_executes g (7:Fin 39) s2 using 1;funext q;fin_cases q <;> rfl
  have hp:(push (6:Fin 39) true).Executes g s3 (prefixState n kind a b left right (k+1) clock) 1:=by
    convert push_executes g (6:Fin 39) true s3 using 1;funext q;fin_cases q <;> rfl
  refine ⟨_,seq_executes _ _ g he (seq_executes _ _ g hu (seq_executes _ _ g hc hp)),?_⟩
  let S:=inputSize n left right
  have hn:n≤ S:=by unfold S inputSize;omega
  have hL:(rowBits (rowPrefix n kind a b left right k)).length≤ 2*(n+1)*(entryExponent S+3):=
    rowPrefix_bits_bound n kind a b left right k ha hb
  have hW:word.length≤ wordBound S:=signedBits_length_of_abs_bound (entry_bound n kind a b left right k ha hb)
  have hM:2*(n+1)*(entryExponent S+3)≤ 2*(S+1)*(entryExponent S+3):=Nat.mul_le_mul_right _ (by omega)
  have henv:(rowBits (rowPrefix n kind a b left right k)).length+k+word.length+1≤ 20*(S+1)^3:=by
    unfold wordBound entryExponent termExponent at hL hW hM
    nlinarith [Nat.zero_le (S^3)]
  have hupdate:=hbb.trans (WordArray.updateBound_polynomial _ _ _)
  change b'≤ 100*((rowBits (rowPrefix n kind a b left right k)).length+k+word.length+1)^2 at hupdate
  have hsq:=Nat.pow_le_pow_left henv 2
  have hW':word.length≤ 2*S^2+5*S+5:=by simpa [CoefficientEntry.wordBound_eq] using hW
  simp only [bodyTime,eval_add,eval_mul,eval_pow,eval_X,eval_ofNat,eval_one]
  change _≤ CoefficientEntry.time.eval S+100000*(S+1)^6
  have hsix:(20*(S+1)^3)^2=400*(S+1)^6:=by ring
  rw [hsix] at hsq
  nlinarith [Nat.zero_le (S^6),Nat.zero_le (S^5),Nat.zero_le (S^4),Nat.zero_le (S^3)]

lemma pop_clock (n : ℕ) (kind : Kind) (a b : ℕ) (left right : List ℕ) (k m : ℕ) :
    Function.update (prefixState n kind a b left right k (m+1)) 8 (List.replicate m true)=
      prefixState n kind a b left right k m:=by funext q;fin_cases q <;> rfl
lemma loop_execution (g : BitString→ ℕ) (n : ℕ) (kind : Kind) (a b : ℕ) (left right : List ℕ)
    (ha:a≤ n) (hb:b≤ n) (hl:left.length=n+1) (hr:right.length=n+1) (k m : ℕ) (hm:k+m≤ n+1) :
    ∃t,WhileExecution (8:Fin 39) (body kind) (body kind) g
      (prefixState n kind a b left right k m) (prefixState n kind a b left right (k+m) 0) t ∧
      t≤ m*(bodyTime.eval (inputSize n left right)+2)+1 := by
  induction m generalizing k with
  | zero=>exact ⟨1,by simpa only [Nat.add_zero] using WhileExecution.empty (prefixState n kind a b left right k 0) rfl,by simp⟩
  | succ m ih=>
    obtain ⟨c,hc,hcb⟩:=body_executes g n kind a b left right ha hb hl hr k m (by omega)
    obtain ⟨t,ht,htb⟩:=ih (k+1) (by omega)
    have h:=WhileExecution.one (show prefixState n kind a b left right k (m+1) 8=true::List.replicate m true from rfl)
      (by rw [pop_clock];exact hc) ht
    refine ⟨1+c+1+t,?_,by nlinarith⟩
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

lemma setup_executes (g : BitString→ ℕ) (n : ℕ) (kind : Kind) (a b : ℕ) (left right : List ℕ) :
    setup.Executes g (store n a b left right []) (prefixState n kind a b left right 0 (n+1)) (42*n+59):=by
  let s1:=state n a b left right 0 n [] []
  let s2:=state n a b left right 0 (n+1) [] []
  let s3:=state n a b left right 0 (n+1) [] [false]
  let s4:=state n a b left right 0 (n+1) (rowBits (rowPrefix n kind a b left right 0)) [false]
  have h0:(copyOn (0:Fin 39) 8 9 (by decide) (by decide) (by decide)).Executes g (store n a b left right []) s1 (5*n+2):=by
    convert copyOn_executes g (0:Fin 39) 8 9 (by decide) (by decide) (by decide) (store n a b left right []) rfl using 1
    · funext q;fin_cases q <;> simp [s1,store,state]
    · simp [store,state]
  have h1:(push (8:Fin 39) true).Executes g s1 s2 1:=by
    convert push_executes g (8:Fin 39) true s1 using 1;funext q;fin_cases q <;> rfl
  have h2:(push (7:Fin 39) false).Executes g s2 s3 1:=by
    convert push_executes g (7:Fin 39) false s2 using 1;funext q;fin_cases q <;> rfl
  have h3:(WordArray.initializeOn initMap).Executes g s3 s4 ((n+1)*37+8):=by
    have h:=WordArray.initializeOn_executes initMap g s3 (n+1) [false] (by funext q;fin_cases q <;> rfl)
    have he:rowBits (rowPrefix n kind a b left right 0)=encodeBitList (List.replicate (n+1) [false]):=by
      rw [rowPrefix_zero]
      simp only [rowBits,rowWords,List.map_replicate]
      rfl
    convert h using 1
    funext q;fin_cases q <;> simp [s4,s3,state,he,initMap]
  have h4:(clear (7:Fin 39)).Executes g s4 (prefixState n kind a b left right 0 (n+1)) 2:=by
    convert clear_executes g (7:Fin 39) s4 using 1;funext q;fin_cases q <;> rfl
  convert seq_executes _ _ g h0 (seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4))) using 1 <;> omega

theorem executes (g : BitString→ ℕ) (n : ℕ) (kind : Kind) (a b : ℕ) (left right : List ℕ)
    (ha:a≤ n) (hb:b≤ n) (hl:left.length=n+1) (hr:right.length=n+1) :
    ∃t,(program kind).Executes g (store n a b left right [])
      (store n a b left right (rowBits (row n kind a b left right))) t ∧t≤ time.eval (inputSize n left right) := by
  obtain ⟨c,hc,hcb⟩:=loop_execution g n kind a b left right ha hb hl hr 0 (n+1) (by omega)
  have hloop:(loop kind).Executes g (prefixState n kind a b left right 0 (n+1))
      (prefixState n kind a b left right (n+1) 0) c:=by
    simpa only [Nat.zero_add] using whilePop_executes _ _ _ g hc
  have hclear:(clear (6:Fin 39)).Executes g (prefixState n kind a b left right (n+1) 0)
      (store n a b left right (rowBits (row n kind a b left right))) (n+2):=by
    convert clear_executes g (6:Fin 39) (prefixState n kind a b left right (n+1) 0) using 1
    · funext q;fin_cases q <;> simp [prefixState,store,state,rowPrefix_complete]
    · simp [prefixState,state]
  refine ⟨_,seq_executes _ _ g (setup_executes g n kind a b left right) (seq_executes _ _ g hloop hclear),?_⟩
  have hN:n≤ inputSize n left right:=by unfold inputSize;omega
  have hm:(n+1)*(bodyTime.eval (inputSize n left right)+2)≤(inputSize n left right+1)*(bodyTime.eval (inputSize n left right)+2):=
    Nat.mul_le_mul_right _ (by omega)
  simp only [time,eval_add,eval_mul,eval_pow,eval_X,eval_ofNat,eval_one]
  nlinarith

lemma body_queryFree (kind : Kind) : (body kind).QueryFree:=seq_queryFree _ _ (CoefficientEntry.on_queryFree _ _)
  (seq_queryFree _ _ (WordArray.updateOn_queryFree _) (seq_queryFree _ _ (clear_queryFree _) (push_queryFree _ _)))
lemma queryFree (kind : Kind) : (program kind).QueryFree:=seq_queryFree _ _
  (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (push_queryFree _ _)
    (seq_queryFree _ _ (push_queryFree _ _) (seq_queryFree _ _ (WordArray.initializeOn_queryFree _) (clear_queryFree _)))))
  (seq_queryFree _ _ (whilePop_queryFree _ _ _ (body_queryFree kind) (body_queryFree kind)) (clear_queryFree _))

noncomputable def on {l : ℕ} (φ : Fin 39↪Fin (l+1)) (kind : Kind) : OracleBlock l:=rename (program kind) φ
lemma on_executes {l : ℕ} (φ : Fin 39↪Fin (l+1)) (g : BitString→ ℕ) (s : Store l)
    (n : ℕ) (kind : Kind) (a b : ℕ) (left right : List ℕ)
    (ha:a≤ n) (hb:b≤ n) (hl:left.length=n+1) (hr:right.length=n+1)
    (hs:s∘φ=store n a b left right []) :
    ∃t,(on φ kind).Executes g s (Function.update s (φ 5) (rowBits (row n kind a b left right))) t ∧
      t≤ time.eval (inputSize n left right) := by
  obtain ⟨t,ht,hb⟩:=executes g n kind a b left right ha hb hl hr
  refine ⟨t,?_,hb⟩
  apply rename_executes_to _ φ g ht hs
  · have he:(Function.update s (φ 5) (rowBits (row n kind a b left right)))∘φ=
        Function.update (s∘φ) 5 (rowBits (row n kind a b left right)):=by
      funext q;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext q;fin_cases q <;> rfl
  · intro q hq;exact Function.update_of_ne (hq 5).symm _ _
lemma on_queryFree {l : ℕ} (φ : Fin 39↪Fin (l+1)) (kind : Kind) : (on φ kind).QueryFree:=rename_queryFree _ _ (queryFree kind)
end HiddenCircuits.DH.Runtime.CoefficientRowRuntime
