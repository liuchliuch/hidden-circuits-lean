import HiddenCircuits.Approximation.SamplerRuntime.RowCheck

/-! A fixed seventeen-stack row switch. It reads both original partners, tests their
new rows against endpoint arrays, conditionally exchanges them, and clears work. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.Switch
open Complexity Complexity.OracleBlock DH.Runtime

def accepts (ls hs ws : List BitString) (i j : ℕ) : Bool :=
  RowCheck.check ls hs i (ws[j]?.getD []) && RowCheck.check ls hs j (ws[i]?.getD [])
def result (ls hs ws : List BitString) (i j : ℕ) : List BitString :=
  if accepts ls hs ws i j then ArraySwap.exchange ws i j else ws

def state (ls hs data : BitString) (i j : ℕ) (left right fa fb : BitString) : Store 16 := fun r =>
  if r.val=0 then ls else if r.val=1 then hs else if r.val=2 then data
  else if r.val=3 then List.replicate i true else if r.val=4 then List.replicate j true
  else if r.val=5 then left else if r.val=6 then right else if r.val=7 then fa else if r.val=8 then fb else []
def leftRead : Fin 8 ↪ Fin 17 where
  toFun i := ![2,3,5,9,10,11,12,13] i
  inj' := by decide +kernel
def rightRead : Fin 8 ↪ Fin 17 where
  toFun i := ![2,4,6,9,10,11,12,13] i
  inj' := by decide +kernel
def leftCheck : Fin 12 ↪ Fin 17 where
  toFun i := ![0,1,3,6,7,9,10,11,12,13,14,15] i
  inj' := by decide +kernel
def rightCheck : Fin 12 ↪ Fin 17 where
  toFun i := ![0,1,4,5,8,9,10,11,12,13,14,15] i
  inj' := by decide +kernel
def swapMap : Fin 10 ↪ Fin 17 where
  toFun i := ![2,3,4,9,10,11,12,13,14,15] i
  inj' := by decide +kernel
noncomputable def guard : OracleBlock 16 := branchPop 7 (clear 8) (clear 8)
  (branchPop 8 skip skip (ArraySwap.on swapMap))
noncomputable def program : OracleBlock 16 := seq (WordArray.readOn leftRead)
  (seq (WordArray.readOn rightRead) (seq (RowCheck.on leftCheck) (seq (RowCheck.on rightCheck)
    (seq guard (seq (clear 5) (clear 6))))))

def bound (ls hs ws : List BitString) (i j : ℕ) : ℕ :=
  GraphReduction.Runtime.lookupBound (encodeBitList ws).length i+
    GraphReduction.Runtime.lookupBound (encodeBitList ws).length j+
    RowCheck.bound ls hs i (ws[j]?.getD [])+RowCheck.bound ls hs j (ws[i]?.getD [])+
    ArraySwap.bound ws i j+(ws[i]?.getD []).length+(ws[j]?.getD []).length+50

lemma pop_left (L H D : BitString) (i j : ℕ) (a b fb : BitString) (bit : Bool) :
    Function.update (state L H D i j a b [bit] fb) 7 []=state L H D i j a b [] fb := by
  funext r;fin_cases r <;> rfl
lemma pop_right (L H D : BitString) (i j : ℕ) (a b : BitString) (bit : Bool) :
    Function.update (state L H D i j a b [] [bit]) 8 []=state L H D i j a b [] [] := by
  funext r;fin_cases r <;> rfl

lemma guard_executes (g : BitString → ℕ) (L H : BitString) (ws : List BitString) (i j : ℕ)
    (a b : BitString) (fa fb : Bool) :
    ∃t,guard.Executes g (state L H (encodeBitList ws) i j a b [fa] [fb])
      (state L H (encodeBitList (if fa&&fb then ArraySwap.exchange ws i j else ws)) i j a b [] []) t ∧
      t≤ArraySwap.bound ws i j+5 := by
  cases fa with
  | false =>
    have hc : (clear (8:Fin 17)).Executes g (state L H (encodeBitList ws) i j a b [] [fb])
        (state L H (encodeBitList ws) i j a b [] []) 2 := by
      convert clear_executes g (8:Fin 17) _ using 1
      funext r;fin_cases r <;> rfl
    exact ⟨4,branchPop_false _ _ _ _ g rfl (by rw [pop_left];exact hc),by omega⟩
  | true =>
    cases fb with
    | false =>
      have hs := skip_executes g (state L H (encodeBitList ws) i j a b [] [])
      have hb := branchPop_false (8:Fin 17) skip skip (ArraySwap.on swapMap) g
        (s:=state L H (encodeBitList ws) i j a b [] [false]) rfl (by rw [pop_right];exact hs)
      exact ⟨5,branchPop_true _ _ _ _ g rfl (by rw [pop_left];exact hb),by omega⟩
    | true =>
      obtain ⟨t,ht,hb⟩ := ArraySwap.on_executes swapMap g
        (state L H (encodeBitList ws) i j a b [] [])
        (state L H (encodeBitList (ArraySwap.exchange ws i j)) i j a b [] []) ws i j
        (by funext r;fin_cases r <;> rfl) (by funext r;fin_cases r <;> rfl)
        (by intro r hr;fin_cases r <;> first | rfl | exact False.elim (hr 0 rfl))
      have hg := branchPop_true (8:Fin 17) skip skip (ArraySwap.on swapMap) g
        (s:=state L H (encodeBitList ws) i j a b [] [true]) rfl (by rw [pop_right];exact ht)
      exact ⟨_,branchPop_true _ _ _ _ g rfl (by rw [pop_left];exact hg),by omega⟩

theorem program_executes (g : BitString → ℕ) (ls hs ws : List BitString) (i j : ℕ) :
    ∃t,program.Executes g (state (encodeBitList ls) (encodeBitList hs) (encodeBitList ws) i j [] [] [] [])
      (state (encodeBitList ls) (encodeBitList hs) (encodeBitList (result ls hs ws i j)) i j [] [] [] []) t ∧
      t≤bound ls hs ws i j := by
  let L := encodeBitList ls
  let H := encodeBitList hs
  let D := encodeBitList ws
  let a := ws[i]?.getD []
  let b := ws[j]?.getD []
  let fa := RowCheck.check ls hs i b
  let fb := RowCheck.check ls hs j a
  obtain ⟨c1,h1,b1⟩ := WordArray.readOn_executes leftRead g (state L H D i j [] [] [] []) ws i
    (by funext r;fin_cases r <;> rfl)
  have e1 : Function.update (state L H D i j [] [] [] []) (leftRead 2) a=state L H D i j a [] [] [] := by
    funext r;fin_cases r <;> rfl
  change (WordArray.readOn leftRead).Executes g _ (Function.update _ (leftRead 2) a) c1 at h1
  rw [e1] at h1
  obtain ⟨c2,h2,b2⟩ := WordArray.readOn_executes rightRead g (state L H D i j a [] [] []) ws j
    (by funext r;fin_cases r <;> rfl)
  have e2 : Function.update (state L H D i j a [] [] []) (rightRead 2) b=state L H D i j a b [] [] := by
    funext r;fin_cases r <;> rfl
  change (WordArray.readOn rightRead).Executes g _ (Function.update _ (rightRead 2) b) c2 at h2
  rw [e2] at h2
  obtain ⟨c3,h3,b3⟩ := RowCheck.on_executes leftCheck g (state L H D i j a b [] []) ls hs i b
    (by funext r;fin_cases r <;> rfl)
  have e3 : Function.update (state L H D i j a b [] []) (leftCheck 4) [fa]=state L H D i j a b [fa] [] := by
    funext r;fin_cases r <;> rfl
  change (RowCheck.on leftCheck).Executes g _ (Function.update _ (leftCheck 4) [fa]) c3 at h3
  rw [e3] at h3
  obtain ⟨c4,h4,b4⟩ := RowCheck.on_executes rightCheck g (state L H D i j a b [fa] []) ls hs j a
    (by funext r;fin_cases r <;> rfl)
  have e4 : Function.update (state L H D i j a b [fa] []) (rightCheck 4) [fb]=state L H D i j a b [fa] [fb] := by
    funext r;fin_cases r <;> rfl
  change (RowCheck.on rightCheck).Executes g _ (Function.update _ (rightCheck 4) [fb]) c4 at h4
  rw [e4] at h4
  obtain ⟨c5,h5,b5⟩ := guard_executes g L H ws i j a b fa fb
  change guard.Executes g _ (state L H (encodeBitList (result ls hs ws i j)) i j a b [] []) c5 at h5
  have h6 : (clear (5:Fin 17)).Executes g (state L H (encodeBitList (result ls hs ws i j)) i j a b [] [])
      (state L H (encodeBitList (result ls hs ws i j)) i j [] b [] []) (a.length+1) := by
    convert clear_executes g (5:Fin 17) _ using 1
    funext r;fin_cases r <;> rfl
  have h7 : (clear (6:Fin 17)).Executes g (state L H (encodeBitList (result ls hs ws i j)) i j [] b [] [])
      (state L H (encodeBitList (result ls hs ws i j)) i j [] [] [] []) (b.length+1) := by
    convert clear_executes g (6:Fin 17) _ using 1
    funext r;fin_cases r <;> rfl
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3
    (seq_executes _ _ g h4 (seq_executes _ _ g h5 (seq_executes _ _ g h6 h7))))),?_⟩
  unfold bound
  dsimp [a,b] at *
  omega

lemma guard_queryFree : guard.QueryFree := branchPop_queryFree _ _ _ _ (clear_queryFree _) (clear_queryFree _)
  (branchPop_queryFree _ _ _ _ skip_queryFree skip_queryFree (ArraySwap.on_queryFree _))
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (WordArray.readOn_queryFree _)
  (seq_queryFree _ _ (WordArray.readOn_queryFree _) (seq_queryFree _ _ (RowCheck.on_queryFree _)
    (seq_queryFree _ _ (RowCheck.on_queryFree _) (seq_queryFree _ _ guard_queryFree
      (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _))))))

end HiddenCircuits.Approximation.SamplerRuntime.Switch
