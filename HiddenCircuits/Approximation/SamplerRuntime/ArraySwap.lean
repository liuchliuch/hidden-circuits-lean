import HiddenCircuits.DH.Runtime.WordArray

/-! A fixed ten-stack two-read/two-update transposition. All addresses and words
are real unary/binary stacks, and every scan/update is charged. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.ArraySwap
open Complexity Complexity.OracleBlock DH.Runtime

/-- Both replacement words are read from the original array. -/
def exchange (ws : List BitString) (i j : ℕ) : List BitString :=
  (ws.set i (ws[j]?.getD [])).set j (ws[i]?.getD [])

def state (data : BitString) (i j : ℕ) (left right : BitString) : Store 9 := fun r =>
  if r.val=0 then data else if r.val=1 then List.replicate i true else if r.val=2 then List.replicate j true
  else if r.val=3 then left else if r.val=4 then right else []

def leftRead : Fin 8 ↪ Fin 10 where
  toFun i := ![0,1,3,5,6,7,8,9] i
  inj' := by decide +kernel
def rightRead : Fin 8 ↪ Fin 10 where
  toFun i := ![0,2,4,5,6,7,8,9] i
  inj' := by decide +kernel
def leftWrite : Fin 8 ↪ Fin 10 where
  toFun i := ![0,1,4,5,6,7,8,9] i
  inj' := by decide +kernel
def rightWrite : Fin 8 ↪ Fin 10 where
  toFun i := ![0,2,3,5,6,7,8,9] i
  inj' := by decide +kernel
noncomputable def program : OracleBlock 9 := seq (WordArray.readOn leftRead)
  (seq (WordArray.readOn rightRead) (seq (WordArray.updateOn leftWrite)
    (seq (WordArray.updateOn rightWrite) (seq (clear 3) (clear 4)))))

def bound (ws : List BitString) (i j : ℕ) : ℕ :=
  let L := (encodeBitList ws).length
  let a := ws[i]?.getD []
  let b := ws[j]?.getD []
  GraphReduction.Runtime.lookupBound L i+GraphReduction.Runtime.lookupBound L j+
    WordArray.updateBound L i b.length+
    WordArray.updateBound (encodeBitList (ws.set i b)).length j a.length+a.length+b.length+20

/-- Total on every canonical word array, including repeated and out-of-range
addresses. The public index stacks are preserved and all work is cleared. -/
theorem program_executes (g : BitString → ℕ) (ws : List BitString) (i j : ℕ) :
    ∃t,program.Executes g (state (encodeBitList ws) i j [] [])
      (state (encodeBitList (exchange ws i j)) i j [] []) t ∧ t≤bound ws i j := by
  let a := ws[i]?.getD []
  let b := ws[j]?.getD []
  obtain ⟨c1,h1,b1⟩ := WordArray.readOn_executes leftRead g (state (encodeBitList ws) i j [] []) ws i
    (by funext r;fin_cases r <;> rfl)
  have e1 : Function.update (state (encodeBitList ws) i j [] []) (leftRead 2) a=
      state (encodeBitList ws) i j a [] := by funext r;fin_cases r <;> rfl
  change (WordArray.readOn leftRead).Executes g _ (Function.update _ (leftRead 2) a) c1 at h1
  rw [e1] at h1
  obtain ⟨c2,h2,b2⟩ := WordArray.readOn_executes rightRead g (state (encodeBitList ws) i j a []) ws j
    (by funext r;fin_cases r <;> rfl)
  have e2 : Function.update (state (encodeBitList ws) i j a []) (rightRead 2) b=
      state (encodeBitList ws) i j a b := by funext r;fin_cases r <;> rfl
  change (WordArray.readOn rightRead).Executes g _ (Function.update _ (rightRead 2) b) c2 at h2
  rw [e2] at h2
  obtain ⟨c3,h3,b3⟩ := WordArray.updateOn_executes leftWrite g (state (encodeBitList ws) i j a b) ws i b
    (by funext r;fin_cases r <;> rfl)
  have e3 : Function.update (state (encodeBitList ws) i j a b) (leftWrite 0) (encodeBitList (ws.set i b))=
      state (encodeBitList (ws.set i b)) i j a b := by funext r;fin_cases r <;> rfl
  rw [e3] at h3
  obtain ⟨c4,h4,b4⟩ := WordArray.updateOn_executes rightWrite g (state (encodeBitList (ws.set i b)) i j a b)
    (ws.set i b) j a (by funext r;fin_cases r <;> rfl)
  have e4 : Function.update (state (encodeBitList (ws.set i b)) i j a b) (rightWrite 0)
      (encodeBitList ((ws.set i b).set j a))=state (encodeBitList (exchange ws i j)) i j a b := by
    funext r;fin_cases r <;> rfl
  rw [e4] at h4
  have h5 : (clear (3:Fin 10)).Executes g (state (encodeBitList (exchange ws i j)) i j a b)
      (state (encodeBitList (exchange ws i j)) i j [] b) (a.length+1) := by
    convert clear_executes g (3:Fin 10) _ using 1
    funext r;fin_cases r <;> rfl
  have h6 : (clear (4:Fin 10)).Executes g (state (encodeBitList (exchange ws i j)) i j [] b)
      (state (encodeBitList (exchange ws i j)) i j [] []) (b.length+1) := by
    convert clear_executes g (4:Fin 10) _ using 1
    funext r;fin_cases r <;> rfl
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3
    (seq_executes _ _ g h4 (seq_executes _ _ g h5 h6)))),?_⟩
  unfold bound
  dsimp [a,b] at *
  omega

lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (WordArray.readOn_queryFree _)
  (seq_queryFree _ _ (WordArray.readOn_queryFree _) (seq_queryFree _ _ (WordArray.updateOn_queryFree _)
    (seq_queryFree _ _ (WordArray.updateOn_queryFree _) (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _)))))

noncomputable def on {k : ℕ} (φ : Fin 10 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 10 ↪ Fin (k+1)) (g : BitString → ℕ) (s t : Store k)
    (ws : List BitString) (i j : ℕ)
    (hs : s∘φ=state (encodeBitList ws) i j [] [])
    (ht : t∘φ=state (encodeBitList (exchange ws i j)) i j [] [])
    (hf : ∀r,(∀q,φ q≠r) → t r=s r) :
    ∃c,(on φ).Executes g s t c ∧ c≤bound ws i j := by
  obtain ⟨c,hc,hb⟩ := program_executes g ws i j
  exact ⟨c,rename_executes_to program φ g hc hs ht hf,hb⟩
lemma on_queryFree {k : ℕ} (φ : Fin 10 ↪ Fin (k+1)) : (on φ).QueryFree :=
  rename_queryFree _ _ program_queryFree

end HiddenCircuits.Approximation.SamplerRuntime.ArraySwap
