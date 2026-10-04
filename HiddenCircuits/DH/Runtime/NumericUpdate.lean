import HiddenCircuits.DH.Runtime.NumericUpdateWrite

/-! Complete query-free update of the three physical
numeric arrays, with a uniform polynomial in n and cleaned work storage. -/
namespace HiddenCircuits.DH.Runtime.NumericUpdate
open Complexity Complexity.OracleBlock NumericStateModel NumericEncoding PruningModel Polynomial
set_option maxHeartbeats 2000000

lemma initial_bound {n : ℕ} (s : NumericStateModel.State n) (h : Safe s) (a : Action n) :
    ∀q,(store n a.keep.val a.removed.val (PairCheck.liveBits s.alive) (sizeBits s) (tableBits s) q).length≤ basePolynomial.eval n := by
  obtain ⟨hn,hL,hS,hT,hR⟩:=base_bounds s h
  have hu:=a.keep.isLt
  have hv:=a.removed.isLt
  intro q
  fin_cases q <;> simp [store,state]
  all_goals first | exact hL | exact hS | exact hT | omega

lemma core_executes (g : BitString→ ℕ) {n : ℕ} (s : NumericStateModel.State n) (h : Safe s) (a : Action n) :
    ∃t,(core a.kind).Executes g (store n a.keep.val a.removed.val (PairCheck.liveBits s.alive) (sizeBits s) (tableBits s))
      (finished s a) t ∧t≤ 20000*(envelope.eval n)^2 := by
  obtain ⟨r,hr,hrb⟩:=reads_executes g s h a
  obtain ⟨m,hm,hmb⟩:=merge_executes g s h a
  have hs:=hm.stack_bound (loaded_bound s h a)
  have hrow:(mergedRow s a).length≤ envelope.eval n:=by
    have hl:=hs (10:Fin 46)
    change (mergedRow s a).length≤ basePolynomial.eval n+m at hl
    have he:=envelope_rowTime n
    omega
  obtain ⟨w,hw,hwb⟩:=writes_executes g s h a hrow
  refine ⟨_,seq_executes _ _ g hr (seq_executes _ _ g hm (seq_executes _ _ g (prepare_executes g s a) hw)),?_⟩
  have hn: n+1≤ basePolynomial.eval n:=(base_bounds s h).1
  have hE:=envelope_base n
  have he:=envelope_rowTime n
  have hA:=h.size_bound a.keep
  have hB:=h.size_bound a.removed
  have hsq:=Nat.pow_le_pow_left (show basePolynomial.eval n≤ envelope.eval n by omega) 2
  nlinarith

/-- Ordinary actual storage update. No graph-class, schedule, or execution
certificate is supplied; `Safe` is the inductively proved numeric invariant. -/
theorem executes (g : BitString→ ℕ) {n : ℕ} (s : NumericStateModel.State n) (h : Safe s) (a : Action n) :
    ∃t,(program a.kind).Executes g
      (store n a.keep.val a.removed.val (PairCheck.liveBits s.alive) (sizeBits s) (tableBits s))
      (store n a.keep.val a.removed.val (PairCheck.liveBits (update s a).alive) (sizeBits (update s a)) (tableBits (update s a))) t ∧
      t≤ time.eval n := by
  obtain ⟨c,hc,hcb⟩:=core_executes g s h a
  have hs:∀q,(finished s a q).length≤ basePolynomial.eval n+c:=hc.stack_bound (initial_bound s h a)
  obtain ⟨d,hd,hdb⟩:=clearList_executes g workPorts (finished s a) _ hs
  have he:eraseStore workPorts (finished s a)=store n a.keep.val a.removed.val
      (PairCheck.liveBits (update s a).alive) (sizeBits (update s a)) (tableBits (update s a)):=by
    funext q;fin_cases q <;> simp [eraseStore,workPorts,finished,store,state]
  rw [he] at hd
  refine ⟨_,seq_executes _ _ g hc hd,?_⟩
  have hn:workPorts.length≤ 46:=(List.length_filter_le _ _).trans (by simp)
  have hd':d≤ 46*(basePolynomial.eval n+c+3)+1:=hdb.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) 1)
  have hb:=envelope_base n
  have hp: n+1≤ basePolynomial.eval n:=(base_bounds s h).1
  have hE:2≤ envelope.eval n:=by omega
  have hh:(envelope.eval n)^2≤(envelope.eval n)^3:=Nat.pow_le_pow_right (by omega) (by decide)
  simp only [time,eval_mul,eval_pow,eval_ofNat]
  nlinarith [Nat.zero_le ((envelope.eval n)^2)]

noncomputable def on {l : ℕ} (φ : Fin 46↪Fin (l+1)) (kind : Kind) : OracleBlock l:=rename (program kind) φ
lemma on_executes {l : ℕ} (φ : Fin 46↪Fin (l+1)) (g : BitString→ ℕ) (before : Store l)
    {n : ℕ} (s : NumericStateModel.State n) (h : Safe s) (a : Action n)
    (hs:before∘φ=store n a.keep.val a.removed.val (PairCheck.liveBits s.alive) (sizeBits s) (tableBits s)) :
    ∃t,(on φ a.kind).Executes g before
      (Function.update (Function.update (Function.update before (φ 2) (PairCheck.liveBits (update s a).alive))
        (φ 3) (sizeBits (update s a))) (φ 4) (tableBits (update s a))) t ∧t≤ time.eval n := by
  obtain ⟨t,ht,hb⟩:=executes g s h a
  refine ⟨t,?_,hb⟩
  apply rename_executes_to _ φ g ht hs
  · funext q
    simp only [Function.comp_def] at hs ⊢
    have hq:=congrFun hs q
    fin_cases q <;> simp_all [Function.update_apply,φ.injective.eq_iff,store,state]
  · intro q hq;simp only [Function.update_of_ne (hq 2).symm,Function.update_of_ne (hq 3).symm,Function.update_of_ne (hq 4).symm]
lemma on_queryFree {l : ℕ} (φ : Fin 46↪Fin (l+1)) (kind : Kind) : (on φ kind).QueryFree:=rename_queryFree _ _ (queryFree kind)
end HiddenCircuits.DH.Runtime.NumericUpdate
