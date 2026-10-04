import HiddenCircuits.DH.Runtime.CoefficientEntryLoops

/-! Complete three-dimensional coefficient loop with
fixed finite code, ordinary row inputs, and physically cleared unary indices. -/
namespace HiddenCircuits.DH.Runtime.CoefficientEntry
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic PruningModel CoefficientRow
open UniformCoefficientModel Polynomial
set_option maxHeartbeats 1800000
noncomputable def planeBody (kind : Kind) : OracleBlock 35:=seq (copyOn 1 10 13 (by decide) (by decide) (by decide))
  (seq (push 10 true) (seq (rowLoop kind) (seq (clear 7) (push 6 true))))
noncomputable def planeLoop (kind : Kind) : OracleBlock 35:=whilePop 11 (planeBody kind) (planeBody kind)
noncomputable def planeTime : Polynomial ℕ:=(X+1)*(rowTime+2)+6*X+20
noncomputable def time : Polynomial ℕ:=(X+1)*(planeTime+2)+6*X+20
noncomputable def program (kind : Kind) : OracleBlock 35:=seq (push 5 false)
  (seq (copyOn 0 11 13 (by decide) (by decide) (by decide)) (seq (push 11 true) (seq (planeLoop kind) (clear 6))))

lemma planeBody_executes (g : BitString→ ℕ) (n : ℕ) (kind : Kind) (left right : List ℕ) (a b k i ci : ℕ)
    (ha:a≤ n) (hb:b≤ n) (hk:k≤ n) (hl:left.length=n+1) (hr:right.length=n+1) (hi:i≤ a) :
    ∃t,(planeBody kind).Executes g (prefixState kind left right a b k i 0 0 ci 0 0)
      (prefixState kind left right a b k (i+1) 0 0 ci 0 0) t ∧ t≤ planeTime.eval (inputSize n left right) := by
  have hc:(copyOn (1:Fin 36) 10 13 (by decide) (by decide) (by decide)).Executes g
      (prefixState kind left right a b k i 0 0 ci 0 0) (prefixState kind left right a b k i 0 0 ci b 0) (5*b+2):=by
    convert copyOn_executes g (1:Fin 36) 10 13 (by decide) (by decide) (by decide)
      (prefixState kind left right a b k i 0 0 ci 0 0) rfl using 1
    · funext q;fin_cases q <;> simp [prefixState,state]
    · simp [prefixState,state]
  have hp:(push (10:Fin 36) true).Executes g (prefixState kind left right a b k i 0 0 ci b 0)
      (prefixState kind left right a b k i 0 0 ci (b+1) 0) 1:=by
    convert push_executes g (10:Fin 36) true (prefixState kind left right a b k i 0 0 ci b 0) using 1
    funext q;fin_cases q <;> rfl
  obtain ⟨c,hc',hcb⟩:=rowLoop_execution g n kind left right a b k i ci ha hb hk hl hr hi 0 (b+1) (by omega)
  have hs:(rowLoop kind).Executes g (prefixState kind left right a b k i 0 0 ci (b+1) 0)
      (prefixState kind left right a b k i (b+1) 0 ci 0 0) c:=by
    simpa only [Nat.zero_add] using whilePop_executes _ _ _ g hc'
  let mid:=state left right a b k i 0 0 ci 0 0 (signedBits (prefixValue kind a b left right k (i+1) 0 0:ℕ)) []
  have hd:(clear (7:Fin 36)).Executes g (prefixState kind left right a b k i (b+1) 0 ci 0 0) mid (b+2):=by
    convert clear_executes g (7:Fin 36) (prefixState kind left right a b k i (b+1) 0 ci 0 0) using 1
    · funext q;fin_cases q <;> simp [prefixState,state,mid,prefix_plane]
    · simp [prefixState,state] <;> omega
  have hi':(push (6:Fin 36) true).Executes g mid (prefixState kind left right a b k (i+1) 0 0 ci 0 0) 1:=by
    convert push_executes g (6:Fin 36) true mid using 1
    funext q;fin_cases q <;> rfl
  refine ⟨_,seq_executes _ _ g hc (seq_executes _ _ g hp (seq_executes _ _ g hs (seq_executes _ _ g hd hi'))),?_⟩
  have hN:n≤ inputSize n left right:=by unfold inputSize;omega
  have hm:(b+1)*(rowTime.eval (inputSize n left right)+2)≤(inputSize n left right+1)*(rowTime.eval (inputSize n left right)+2):=
    Nat.mul_le_mul_right _ (by omega)
  simp only [planeTime,eval_add,eval_mul,eval_X,eval_ofNat,eval_one]
  omega
lemma pop_iclock (kind : Kind) (left right : List ℕ) (a b k i m : ℕ) :
    Function.update (prefixState kind left right a b k i 0 0 (m+1) 0 0) 11 (List.replicate m true)=
      prefixState kind left right a b k i 0 0 m 0 0:=by funext q;fin_cases q <;> rfl
lemma planeLoop_execution (g : BitString→ ℕ) (n : ℕ) (kind : Kind) (left right : List ℕ) (a b k : ℕ)
    (ha:a≤ n) (hb:b≤ n) (hk:k≤ n) (hl:left.length=n+1) (hr:right.length=n+1)
    (i m : ℕ) (hm:i+m≤ a+1) :
    ∃t,WhileExecution (11:Fin 36) (planeBody kind) (planeBody kind) g
      (prefixState kind left right a b k i 0 0 m 0 0)
      (prefixState kind left right a b k (i+m) 0 0 0 0 0) t ∧
      t≤ m*(planeTime.eval (inputSize n left right)+2)+1 := by
  induction m generalizing i with
  | zero=>exact ⟨1,by simpa only [Nat.add_zero] using WhileExecution.empty (prefixState kind left right a b k i 0 0 0 0 0) rfl,by simp⟩
  | succ m ih=>
    obtain ⟨c,hc,hcb⟩:=planeBody_executes g n kind left right a b k i m ha hb hk hl hr (by omega)
    obtain ⟨t,ht,htb⟩:=ih (i+1) (by omega)
    have h:=WhileExecution.one (show prefixState kind left right a b k i 0 0 (m+1) 0 0 11=true::List.replicate m true from rfl)
      (by rw [pop_iclock];exact hc) ht
    refine ⟨1+c+1+t,?_,by nlinarith⟩
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem executes (g : BitString→ ℕ) (n : ℕ) (kind : Kind) (left right : List ℕ) (a b k : ℕ)
    (ha:a≤ n) (hb:b≤ n) (hk:k≤ n) (hl:left.length=n+1) (hr:right.length=n+1) :
    ∃t,(program kind).Executes g (store left right a b k [])
      (store left right a b k (signedBits (entry kind a b left right k:ℕ))) t ∧
      t≤ time.eval (inputSize n left right) := by
  have hp0:(push (5:Fin 36) false).Executes g (store left right a b k [])
      (prefixState kind left right a b k 0 0 0 0 0 0) 1:=by
    convert push_executes g (5:Fin 36) false (store left right a b k []) using 1
    funext q;fin_cases q <;> simp [prefixState,store,state,prefix_zero,signedBits,negative,Computability.encodeNat]
    rfl
  have hc:(copyOn (0:Fin 36) 11 13 (by decide) (by decide) (by decide)).Executes g
      (prefixState kind left right a b k 0 0 0 0 0 0) (prefixState kind left right a b k 0 0 0 a 0 0) (5*a+2):=by
    convert copyOn_executes g (0:Fin 36) 11 13 (by decide) (by decide) (by decide)
      (prefixState kind left right a b k 0 0 0 0 0 0) rfl using 1
    · funext q;fin_cases q <;> simp [prefixState,state]
    · simp [prefixState,state]
  have hp:(push (11:Fin 36) true).Executes g (prefixState kind left right a b k 0 0 0 a 0 0)
      (prefixState kind left right a b k 0 0 0 (a+1) 0 0) 1:=by
    convert push_executes g (11:Fin 36) true (prefixState kind left right a b k 0 0 0 a 0 0) using 1
    funext q;fin_cases q <;> rfl
  obtain ⟨c,hc',hcb⟩:=planeLoop_execution g n kind left right a b k ha hb hk hl hr 0 (a+1) (by omega)
  have hs:(planeLoop kind).Executes g (prefixState kind left right a b k 0 0 0 (a+1) 0 0)
      (prefixState kind left right a b k (a+1) 0 0 0 0 0) c:=by
    simpa only [Nat.zero_add] using whilePop_executes _ _ _ g hc'
  have hd:(clear (6:Fin 36)).Executes g (prefixState kind left right a b k (a+1) 0 0 0 0 0)
      (store left right a b k (signedBits (entry kind a b left right k:ℕ))) (a+2):=by
    convert clear_executes g (6:Fin 36) (prefixState kind left right a b k (a+1) 0 0 0 0 0) using 1
    · funext q;fin_cases q <;> simp [prefixState,store,state,prefix_complete]
    · simp [prefixState,state] <;> omega
  refine ⟨_,seq_executes _ _ g hp0 (seq_executes _ _ g hc (seq_executes _ _ g hp (seq_executes _ _ g hs hd))),?_⟩
  have hN:n≤ inputSize n left right:=by unfold inputSize;omega
  have hm:(a+1)*(planeTime.eval (inputSize n left right)+2)≤(inputSize n left right+1)*(planeTime.eval (inputSize n left right)+2):=
    Nat.mul_le_mul_right _ (by omega)
  simp only [time,eval_add,eval_mul,eval_X,eval_ofNat,eval_one]
  omega
lemma planeBody_queryFree (kind : Kind) : (planeBody kind).QueryFree:=seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (push_queryFree _ _) (seq_queryFree _ _ (rowLoop_queryFree kind)
    (seq_queryFree _ _ (clear_queryFree _) (push_queryFree _ _))))
lemma planeLoop_queryFree (kind : Kind) : (planeLoop kind).QueryFree:=whilePop_queryFree _ _ _ (planeBody_queryFree kind) (planeBody_queryFree kind)
lemma queryFree (kind : Kind) : (program kind).QueryFree:=seq_queryFree _ _ (push_queryFree _ _)
  (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (push_queryFree _ _)
    (seq_queryFree _ _ (planeLoop_queryFree kind) (clear_queryFree _))))
noncomputable def on {l : ℕ} (φ : Fin 36↪Fin (l+1)) (kind : Kind) : OracleBlock l:=rename (program kind) φ
lemma on_executes {l : ℕ} (φ : Fin 36↪Fin (l+1)) (g : BitString→ ℕ) (s : Store l)
    (n : ℕ) (kind : Kind) (left right : List ℕ) (a b k : ℕ)
    (ha:a≤ n) (hb:b≤ n) (hk:k≤ n) (hl:left.length=n+1) (hr:right.length=n+1)
    (hs:s∘φ=store left right a b k []) :
    ∃t,(on φ kind).Executes g s
      (Function.update s (φ 5) (signedBits (entry kind a b left right k:ℕ))) t ∧
      t≤ time.eval (inputSize n left right) := by
  obtain ⟨t,ht,hb⟩:=executes g n kind left right a b k ha hb hk hl hr
  refine ⟨t,?_,hb⟩
  apply rename_executes_to _ φ g ht hs
  · have he:(Function.update s (φ 5) (signedBits (entry kind a b left right k:ℕ)))∘φ=
        Function.update (s∘φ) 5 (signedBits (entry kind a b left right k:ℕ)):=by
      funext q;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext q;fin_cases q <;> rfl
  · intro q hq;exact Function.update_of_ne (hq 5).symm _ _
lemma on_queryFree {l : ℕ} (φ : Fin 36↪Fin (l+1)) (kind : Kind) : (on φ kind).QueryFree:=rename_queryFree _ _ (queryFree kind)
end HiddenCircuits.DH.Runtime.CoefficientEntry
