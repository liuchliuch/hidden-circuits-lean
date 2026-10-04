import HiddenCircuits.Complexity.OracleRepeat
import HiddenCircuits.DH.Runtime.WordArrayInitialize
import HiddenCircuits.DH.Runtime.StorageBounds

/-! Dynamic live marks, sizes and the full coefficient
table are physically allocated from the ordinary unary graph size. -/
namespace HiddenCircuits.DH.Runtime.NumericInitialize
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic
set_option maxHeartbeats 1600000

def state (n : ℕ) (live sizes table nn row zero one oneWord : BitString) : Store 13:=fun q=>
  if q.val=0 then List.replicate n true else if q.val=1 then live else if q.val=2 then sizes else if q.val=3 then table
  else if q.val=4 then nn else if q.val=5 then row else if q.val=6 then zero else if q.val=7 then one
  else if q.val=8 then oneWord else []
def store (n : ℕ) (live sizes table : BitString) : Store 13:=state n live sizes table [] [] [] [] []
def rowInitMap : Fin 8↪Fin 14:=⟨fun q=>![5,4,6,9,10,11,12,13] q,by decide +kernel⟩
def rowUpdateMap : Fin 8↪Fin 14:=⟨fun q=>![5,7,8,9,10,11,12,13] q,by decide +kernel⟩
def tableMap : Fin 8↪Fin 14:=⟨fun q=>![3,0,5,9,10,11,12,13] q,by decide +kernel⟩
def sizesMap : Fin 8↪Fin 14:=⟨fun q=>![2,0,7,9,10,11,12,13] q,by decide +kernel⟩
noncomputable def setup : OracleBlock 13:=seq (copyOn 0 4 9 (by decide) (by decide) (by decide))
  (seq (push 4 true) (seq (push 6 false) (seq (push 7 true) (prepend 8 [false,true]))))
noncomputable def core : OracleBlock 13:=seq setup (seq (WordArray.initializeOn rowInitMap)
  (seq (WordArray.updateOn rowUpdateMap) (seq (WordArray.initializeOn tableMap)
    (seq (WordArray.initializeOn sizesMap) (copyOn 2 1 9 (by decide) (by decide) (by decide))))))
def workPorts : List (Fin 14):=(List.finRange 14).filter (fun q=>4≤ q.val)
noncomputable def program : OracleBlock 13:=seq core (clearList workPorts)
noncomputable def time : Polynomial ℕ:=100000*(Polynomial.X+1)^3

def ready (n : ℕ) (live sizes table row : BitString) : Store 13:=
  state n live sizes table (List.replicate (n+1) true) row [false] [true] [false,true]
lemma setup_executes (g : BitString→ ℕ) (n : ℕ) : setup.Executes g (store n [] [] []) (ready n [] [] [] []) (5*n+20):=by
  let s0:=store n [] [] []
  let s1:=Function.update s0 4 (List.replicate n true)
  let s2:=Function.update s1 4 (List.replicate (n+1) true)
  let s3:=Function.update s2 6 [false]
  let s4:=Function.update s3 7 [true]
  have h0:(copyOn (0:Fin 14) 4 9 (by decide) (by decide) (by decide)).Executes g s0 s1 (5*n+2):=by
    convert copyOn_executes g (0:Fin 14) 4 9 (by decide) (by decide) (by decide) s0 rfl using 1
    · funext q;fin_cases q <;> simp [s0,s1,store,state]
    · simp [s0,store,state]
  have h1:(push (4:Fin 14) true).Executes g s1 s2 1:=by
    convert push_executes g (4:Fin 14) true s1 using 1 <;> (funext q;fin_cases q <;> rfl)
  have h2:(push (6:Fin 14) false).Executes g s2 s3 1:=by
    convert push_executes g (6:Fin 14) false s2 using 1 <;> (funext q;fin_cases q <;> rfl)
  have h3:(push (7:Fin 14) true).Executes g s3 s4 1:=by
    convert push_executes g (7:Fin 14) true s3 using 1 <;> (funext q;fin_cases q <;> rfl)
  have h4:(prepend (8:Fin 14) [false,true]).Executes g s4 (ready n [] [] [] []) 7:=by
    convert prepend_executes g (8:Fin 14) [false,true] s4 using 1 <;> (funext q;fin_cases q <;> rfl)
  convert seq_executes _ _ g h0 (seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4))) using 1 <;> omega

theorem core_executes (g : BitString→ ℕ) (n : ℕ) :
    ∃t,core.Executes g (store n [] [] [])
      (ready n (PairCheck.liveBits (NumericStateModel.initial n).alive)
        (NumericEncoding.sizeBits (NumericStateModel.initial n)) (NumericEncoding.tableBits (NumericStateModel.initial n))
        (NumericEncoding.rowBits (CoefficientModel.leafRow n))) t ∧ t≤ 1000*(n+1)^2 := by
  let zrow:=encodeBitList (List.replicate (n+1) [false])
  let row:=encodeBitList ((List.replicate (n+1) [false]).set 1 [false,true])
  let tab:=encodeBitList (List.replicate n row)
  let sz:=encodeBitList (List.replicate n [true])
  have h1:(WordArray.initializeOn rowInitMap).Executes g (ready n [] [] [] []) (ready n [] [] [] zrow) ((n+1)*37+8):=by
    have h:=WordArray.initializeOn_executes rowInitMap g (ready n [] [] [] []) (n+1) [false]
      (by funext q;fin_cases q <;> rfl)
    convert h using 1 <;> (funext q;fin_cases q <;> rfl)
  obtain ⟨c,hc,hcb⟩:=WordArray.updateOn_executes rowUpdateMap g (ready n [] [] [] zrow)
    (List.replicate (n+1) [false]) 1 [false,true] (by funext q;fin_cases q <;> rfl)
  have h2:(WordArray.updateOn rowUpdateMap).Executes g (ready n [] [] [] zrow) (ready n [] [] [] row) c:=by
    convert hc using 1 <;> (funext q;fin_cases q <;> rfl)
  have h3:(WordArray.initializeOn tableMap).Executes g (ready n [] [] [] row) (ready n [] [] tab row)
      (n*(15*row.length+22)+8):=by
    have h:=WordArray.initializeOn_executes tableMap g (ready n [] [] [] row) n row (by funext q;fin_cases q <;> rfl)
    convert h using 1 <;> (funext q;fin_cases q <;> rfl)
  have h4:(WordArray.initializeOn sizesMap).Executes g (ready n [] [] tab row) (ready n [] sz tab row) (n*37+8):=by
    have h:=WordArray.initializeOn_executes sizesMap g (ready n [] [] tab row) n [true] (by funext q;fin_cases q <;> rfl)
    convert h using 1 <;> (funext q;fin_cases q <;> rfl)
  have h5:(copyOn (2:Fin 14) 1 9 (by decide) (by decide) (by decide)).Executes g (ready n [] sz tab row)
      (ready n sz sz tab row) (5*sz.length+2):=by
    convert copyOn_executes g (2:Fin 14) 1 9 (by decide) (by decide) (by decide) (ready n [] sz tab row) rfl using 1
    funext q;fin_cases q <;> simp [ready,state]
  have hrow:row=NumericEncoding.rowBits (CoefficientModel.leafRow n):=by
    simp [row,NumericEncoding.rowBits,NumericEncoding.leaf_words]
  have hsz:sz=NumericEncoding.sizeBits (NumericStateModel.initial n):= (NumericEncoding.initial_sizes n).symm
  have hlive:sz=PairCheck.liveBits (NumericStateModel.initial n).alive:= (NumericEncoding.initial_alive n).symm
  have htab:tab=NumericEncoding.tableBits (NumericStateModel.initial n):=(NumericEncoding.initial_table n).symm
  have hh:=seq_executes _ _ g (setup_executes g n) (seq_executes _ _ g h1 (seq_executes _ _ g h2
    (seq_executes _ _ g h3 (seq_executes _ _ g h4 h5))))
  have he:ready n sz sz tab row=ready n (PairCheck.liveBits (NumericStateModel.initial n).alive)
      (NumericEncoding.sizeBits (NumericStateModel.initial n)) (NumericEncoding.tableBits (NumericStateModel.initial n))
      (NumericEncoding.rowBits (CoefficientModel.leafRow n)):=by rw [←hrow,←hsz,←htab,←hlive]
  rw [he] at hh
  refine ⟨_,hh,?_⟩
  have hz:zrow.length=4*(n+1):=by simp [zrow,encodeBitList_length];ring
  have hszlen:sz.length=4*n:=by simp [sz,encodeBitList_length];ring
  have hr:row.length≤ 6*(n+1):=by
      have hw:∀w∈((List.replicate (n+1) [false]).set 1 [false,true]),w.length≤ 2:=by
        intro w hw
        have hh:=List.mem_or_eq_of_mem_set hw
        rcases hh with h|h
        · have := List.mem_replicate.mp h;rcases this with ⟨_,rfl⟩;decide
        · subst w;decide
      have hs:=NumericEncoding.sum_length_le ((List.replicate (n+1) [false]).set 1 [false,true]) 2 hw
      simp only [List.length_set,List.length_replicate] at hs
      simp only [row,encodeBitList_length,List.length_set,List.length_replicate]
      omega
  change c≤ WordArray.updateBound zrow.length 1 2 at hcb
  rw [hz] at hcb
  unfold WordArray.updateBound at hcb
  rw [hszlen]
  have hm:=Nat.mul_le_mul_left (15*n) hr
  nlinarith

theorem executes (g : BitString→ ℕ) (n : ℕ) :
    ∃t,program.Executes g (store n [] [] [])
      (store n (PairCheck.liveBits (NumericStateModel.initial n).alive)
        (NumericEncoding.sizeBits (NumericStateModel.initial n)) (NumericEncoding.tableBits (NumericStateModel.initial n))) t ∧
      t≤ time.eval n := by
  obtain ⟨c,hc,hcb⟩:=core_executes g n
  let out:=ready n (PairCheck.liveBits (NumericStateModel.initial n).alive)
    (NumericEncoding.sizeBits (NumericStateModel.initial n)) (NumericEncoding.tableBits (NumericStateModel.initial n))
    (NumericEncoding.rowBits (CoefficientModel.leafRow n))
  have hb:∀q,(out q).length≤ n+c:=hc.stack_bound (by intro q;change (store n [] [] [] q).length≤n;fin_cases q <;> simp [store,state])
  obtain ⟨d,hd,hdb⟩:=clearList_executes g workPorts out (n+c) hb
  have he:eraseStore workPorts out=store n (PairCheck.liveBits (NumericStateModel.initial n).alive)
      (NumericEncoding.sizeBits (NumericStateModel.initial n)) (NumericEncoding.tableBits (NumericStateModel.initial n)):=by
    funext q;fin_cases q <;> simp [eraseStore,workPorts,out,ready,store,state]
  rw [he] at hd
  refine ⟨_,seq_executes _ _ g hc hd,?_⟩
  have hn:workPorts.length≤ 14:=(List.length_filter_le _ _).trans (by simp)
  have hd':d≤ 14*(n+c+3)+1:=hdb.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) 1)
  simp only [time,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]
  nlinarith [Nat.zero_le (n^3)]

lemma queryFree : program.QueryFree:=seq_queryFree _ _ (seq_queryFree _ _
  (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (push_queryFree _ _)
    (seq_queryFree _ _ (push_queryFree _ _) (seq_queryFree _ _ (push_queryFree _ _) (prepend_queryFree _ _)))))
  (seq_queryFree _ _ (WordArray.initializeOn_queryFree _) (seq_queryFree _ _ (WordArray.updateOn_queryFree _)
    (seq_queryFree _ _ (WordArray.initializeOn_queryFree _) (seq_queryFree _ _ (WordArray.initializeOn_queryFree _)
      (copyOn_queryFree _ _ _ _ _ _)))))) (clearList_queryFree _)
noncomputable def on {l : ℕ} (φ : Fin 14↪Fin (l+1)) : OracleBlock l:=rename program φ
lemma on_executes {l : ℕ} (φ : Fin 14↪Fin (l+1)) (g : BitString→ ℕ) (s : Store l) (n : ℕ)
    (hs:s∘φ=store n [] [] []) :
    ∃t,(on φ).Executes g s
      (Function.update (Function.update (Function.update s (φ 1) (PairCheck.liveBits (NumericStateModel.initial n).alive))
        (φ 2) (NumericEncoding.sizeBits (NumericStateModel.initial n))) (φ 3) (NumericEncoding.tableBits (NumericStateModel.initial n))) t ∧
      t≤ time.eval n := by
  obtain ⟨t,ht,hb⟩:=executes g n
  refine ⟨t,?_,hb⟩
  apply rename_executes_to _ φ g ht hs
  · funext q
    simp only [Function.comp_def] at hs ⊢
    have hq:=congrFun hs q
    fin_cases q <;> simp_all [Function.update_apply,φ.injective.eq_iff,store,state]
  · intro q hq;simp only [Function.update_of_ne (hq 1).symm,Function.update_of_ne (hq 2).symm,Function.update_of_ne (hq 3).symm]
lemma on_queryFree {l : ℕ} (φ : Fin 14↪Fin (l+1)) : (on φ).QueryFree:=rename_queryFree _ _ queryFree
end HiddenCircuits.DH.Runtime.NumericInitialize
