import HiddenCircuits.Approximation.SamplerRuntime.EndpointParserRowAux

/-! Fresh endpoint-row reconstruction. Each row is physically parsed, both
unary representations are checked, and all four endpoint inequalities are
computed by charged read-only bit-length comparisons. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.EndpointParser.Scan
open Complexity OracleBlock GraphVerifier GraphVerifier.Runtime
set_option maxHeartbeats 900000

structure State where
  header : BitString
  prevLo : BitString
  prevHi : BitString
  lows : BitString
  highs : BitString
  valid : Bool

def Bounded (N : ℕ) (s : State) : Prop :=
  s.header.length≤N ∧ s.prevLo.length≤N ∧ s.prevHi.length≤N ∧ s.lows.length≤N ∧ s.highs.length≤N

def low (s : State) := headResult s.lows
def high (s : State) := headResult s.highs

def rowValid (s : State) : Bool :=
  s.valid && (low s).ok && (high s).ok && (low s).left.all id && (high s).left.all id &&
    decide (s.prevLo.length≤(low s).left.length) && decide (s.prevHi.length≤(high s).left.length) &&
    decide ((low s).left.length≤(high s).left.length) && decide ((high s).left.length≤s.header.length)

def step (s : State) : State :=
  ⟨s.header,(low s).left,(high s).left,(low s).right,(high s).right,rowValid s⟩

def store (s : State) (clock : BitString) : Store 23 := fun i =>
  if i.val=0 then s.header else if i.val=1 then s.prevLo else if i.val=2 then s.prevHi
  else if i.val=3 then s.lows else if i.val=4 then s.highs else if i.val=5 then [s.valid]
  else if i.val=11 then clock else []

def headLowMap : Fin 4 ↪ Fin 24 where
  toFun i := ![3,7,19,9] i
  inj' := by decide +kernel
def headHighMap : Fin 4 ↪ Fin 24 where
  toFun i := ![4,8,19,10] i
  inj' := by decide +kernel
def unaryLowMap : Fin 3 ↪ Fin 24 where
  toFun i := ![7,12,19] i
  inj' := by decide +kernel
def unaryHighMap : Fin 3 ↪ Fin 24 where
  toFun i := ![8,13,19] i
  inj' := by decide +kernel
def cmpLowMap : Fin 6 ↪ Fin 24 where
  toFun i := ![7,1,14,19,20,21] i
  inj' := by decide +kernel
def cmpHighMap : Fin 6 ↪ Fin 24 where
  toFun i := ![8,2,15,19,20,21] i
  inj' := by decide +kernel
def cmpCrossMap : Fin 6 ↪ Fin 24 where
  toFun i := ![8,7,16,19,20,21] i
  inj' := by decide +kernel
def cmpBoundMap : Fin 6 ↪ Fin 24 where
  toFun i := ![0,8,17,19,20,21] i
  inj' := by decide +kernel

def afterLow (s : State) (clock : BitString) : Store 23 :=
  Function.update (Function.update (Function.update (store s clock) 3 (low s).right) 7 (low s).left) 9 [(low s).ok]
def afterHeads (s : State) (clock : BitString) : Store 23 :=
  Function.update (Function.update (Function.update (afterLow s clock) 4 (high s).right) 8 (high s).left) 10 [(high s).ok]
def afterUnaryLow (s : State) (clock : BitString) : Store 23 := Function.update (afterHeads s clock) 12 [(low s).left.all id]
def afterUnary (s : State) (clock : BitString) : Store 23 := Function.update (afterUnaryLow s clock) 13 [(high s).left.all id]
def afterCmpLow (s : State) (clock : BitString) : Store 23 := Function.update (afterUnary s clock) 14 [decide (s.prevLo.length≤(low s).left.length)]
def afterCmpHigh (s : State) (clock : BitString) : Store 23 := Function.update (afterCmpLow s clock) 15 [decide (s.prevHi.length≤(high s).left.length)]
def afterCmpCross (s : State) (clock : BitString) : Store 23 := Function.update (afterCmpHigh s clock) 16 [decide ((low s).left.length≤(high s).left.length)]
def checked (s : State) (clock : BitString) : Store 23 := Function.update (afterCmpCross s clock) 17 [decide ((high s).left.length≤s.header.length)]

def rowInputs : List (Fin 24) := [5,9,10,12,13,14,15,16,17]
def rowBits (s : State) (i : Fin 24) : Bool :=
  if i.val=5 then s.valid else if i.val=9 then (low s).ok else if i.val=10 then (high s).ok
  else if i.val=12 then (low s).left.all id else if i.val=13 then (high s).left.all id
  else if i.val=14 then decide (s.prevLo.length≤(low s).left.length)
  else if i.val=15 then decide (s.prevHi.length≤(high s).left.length)
  else if i.val=16 then decide ((low s).left.length≤(high s).left.length)
  else decide ((high s).left.length≤s.header.length)
def decided (s : State) (clock : BitString) : Store 23 :=
  Function.update (eraseStore rowInputs (checked s clock)) 6 [rowValid s]
def transferred (s : State) (clock : BitString) : Store 23 :=
  Function.update (Function.update (decided s clock) 6 []) 5 [rowValid s]
def replacedLow (s : State) (clock : BitString) : Store 23 :=
  Function.update (Function.update (transferred s clock) 1 (low s).left) 7 []

noncomputable def headPhase : OracleBlock 23 := seq (headOn headLowMap) (headOn headHighMap)
noncomputable def unaryPhase : OracleBlock 23 := seq (unaryReadOn unaryLowMap) (unaryReadOn unaryHighMap)
noncomputable def comparePhase : OracleBlock 23 := seq (readAtLeastOn cmpLowMap)
  (seq (readAtLeastOn cmpHighMap) (seq (readAtLeastOn cmpCrossMap) (readAtLeastOn cmpBoundMap)))
noncomputable def finishRow : OracleBlock 23 := seq (decision 6 rowInputs (fun bs => bs.all id))
  (seq (reverseOn 6 5 (by decide)) (seq (replaceOn 7 1 19 (by decide) (by decide) (by decide))
    (replaceOn 8 2 19 (by decide) (by decide) (by decide))))
noncomputable def row : OracleBlock 23 := seq headPhase (seq unaryPhase (seq comparePhase finishRow))

theorem headPhase_executes (g : BitString → ℕ) (s : State) (clock : BitString) :
    headPhase.Executes g (store s clock) (afterHeads s clock) (headCost s.lows+headCost s.highs+2) := by
  have h₁ : (headOn headLowMap).Executes g (store s clock) (afterLow s clock) (headCost s.lows) := by
    apply headOn_executes _ g _ _ s.lows
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
    · intro i hi; fin_cases i <;> first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 3 rfl)
  have h₂ : (headOn headHighMap).Executes g (afterLow s clock) (afterHeads s clock) (headCost s.highs) := by
    apply headOn_executes _ g _ _ s.highs
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
    · intro i hi; fin_cases i <;> first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 3 rfl)
  exact seq_executes _ _ g h₁ h₂

theorem unaryPhase_executes (g : BitString → ℕ) (s : State) (clock : BitString) :
    unaryPhase.Executes g (afterHeads s clock) (afterUnary s clock)
      (6*(low s).left.length+6*(high s).left.length+14) := by
  have h₁ := unaryReadOn_executes unaryLowMap g (afterHeads s clock) (low s).left (by funext i; fin_cases i <;> rfl)
  have h₂ := unaryReadOn_executes unaryHighMap g (afterUnaryLow s clock) (high s).left (by funext i; fin_cases i <;> rfl)
  convert seq_executes _ _ g h₁ h₂ using 1 <;> omega

theorem comparePhase_executes (g : BitString → ℕ) (s : State) (clock : BitString) (N : ℕ) (h : Bounded N s) :
    ∃c, comparePhase.Executes g (afterUnary s clock) (checked s clock) c ∧ c≤104*N+98 := by
  obtain ⟨a,ha,hab⟩ := readAtLeastOn_executes cmpLowMap g (afterUnary s clock) (low s).left s.prevLo (by funext i; fin_cases i <;> rfl)
  obtain ⟨b,hb,hbb⟩ := readAtLeastOn_executes cmpHighMap g (afterCmpLow s clock) (high s).left s.prevHi (by funext i; fin_cases i <;> rfl)
  obtain ⟨c,hc,hcb⟩ := readAtLeastOn_executes cmpCrossMap g (afterCmpHigh s clock) (high s).left (low s).left (by funext i; fin_cases i <;> rfl)
  obtain ⟨d,hd,hdb⟩ := readAtLeastOn_executes cmpBoundMap g (afterCmpCross s clock) s.header (high s).left (by funext i; fin_cases i <;> rfl)
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb (seq_executes _ _ g hc hd)),?_⟩
  have hl := (head_lengths s.lows).1
  have hh := (head_lengths s.highs).1
  change (low s).left.length≤s.lows.length at hl
  change (high s).left.length≤s.highs.length at hh
  rcases h with ⟨h₀,h₁,h₂,h₃,h₄⟩
  omega

theorem finishRow_executes (g : BitString → ℕ) (s : State) (clock : BitString) :
    finishRow.Executes g (checked s clock) (store (step s) clock)
      (6*(low s).left.length+6*(high s).left.length+s.prevLo.length+s.prevHi.length+47) := by
  have h₁ : (decision (6:Fin 24) rowInputs (fun bs => bs.all id)).Executes g (checked s clock) (decided s clock) 22 := by
    have hh := decision_executes (6:Fin 24) rowInputs (by decide +kernel) (by decide +kernel)
      (fun bs => bs.all id) (rowBits s) g (checked s clock) (by
        intro i hi; simp only [rowInputs,List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl)
    have he : (rowInputs.map (rowBits s)).all id=rowValid s := by
      simp [rowInputs,rowBits,rowValid,Bool.and_assoc]
    simpa only [he] using hh
  have h₂ : (reverseOn (6:Fin 24) 5 (by decide)).Executes g (decided s clock) (transferred s clock) 3 := by
    exact reverseOn_executes g (6:Fin 24) 5 (by decide) (decided s clock)
  have h₃ : (replaceOn (7:Fin 24) 1 19 (by decide) (by decide) (by decide)).Executes g (transferred s clock) (replacedLow s clock)
      (6*(low s).left.length+s.prevLo.length+8) := by
    exact replaceOn_executes 7 1 19 (by decide) (by decide) (by decide) g (transferred s clock) rfl
  have h₄ : (replaceOn (8:Fin 24) 2 19 (by decide) (by decide) (by decide)).Executes g (replacedLow s clock) (store (step s) clock)
      (6*(high s).left.length+s.prevHi.length+8) := by
    convert replaceOn_executes (8:Fin 24) 2 19 (by decide) (by decide) (by decide) g (replacedLow s clock) rfl using 1
    funext i; fin_cases i <;> simp [replacedLow,transferred,decided,eraseStore,rowInputs,checked,afterCmpCross,afterCmpHigh,afterCmpLow,afterUnary,afterUnaryLow,afterHeads,afterLow,store,step]
  convert seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ h₄)) using 1 <;> omega

theorem row_executes (g : BitString → ℕ) (s : State) (clock : BitString) (N : ℕ) (h : Bounded N s) :
    ∃c, row.Executes g (store s clock) (store (step s) clock) c ∧ c≤2000*(N+1) := by
  obtain ⟨c,hc,hcb⟩ := comparePhase_executes g s clock N h
  refine ⟨_,seq_executes _ _ g (headPhase_executes g s clock)
    (seq_executes _ _ g (unaryPhase_executes g s clock)
      (seq_executes _ _ g hc (finishRow_executes g s clock))),?_⟩
  have hcl := head_cost_bound s.lows
  have hch := head_cost_bound s.highs
  have hl := (head_lengths s.lows).1
  have hh := (head_lengths s.highs).1
  change (low s).left.length≤s.lows.length at hl
  change (high s).left.length≤s.highs.length at hh
  rcases h with ⟨h₀,h₁,h₂,h₃,h₄⟩
  omega

lemma step_bounded (N : ℕ) (s : State) (h : Bounded N s) : Bounded N (step s) := by
  have hl := head_lengths s.lows
  have hh := head_lengths s.highs
  exact ⟨h.1,hl.1.trans h.2.2.2.1,hh.1.trans h.2.2.2.2,hl.2.trans h.2.2.2.1,hh.2.trans h.2.2.2.2⟩
lemma row_queryFree : row.QueryFree :=
  seq_queryFree _ _ (seq_queryFree _ _ (headOn_queryFree _) (headOn_queryFree _))
    (seq_queryFree _ _ (seq_queryFree _ _ (unaryReadOn_queryFree _) (unaryReadOn_queryFree _))
      (seq_queryFree _ _ (seq_queryFree _ _ (readAtLeastOn_queryFree _)
        (seq_queryFree _ _ (readAtLeastOn_queryFree _) (seq_queryFree _ _ (readAtLeastOn_queryFree _) (readAtLeastOn_queryFree _))))
        (seq_queryFree _ _ (decision_queryFree _ _ _)
          (seq_queryFree _ _ (reverseOn_queryFree _ _ _) (seq_queryFree _ _ (replaceOn_queryFree _ _ _ _ _ _) (replaceOn_queryFree _ _ _ _ _ _))))))
end HiddenCircuits.Approximation.SamplerRuntime.EndpointParser.Scan
