import HiddenCircuits.DH.Runtime.UnaryFor
import HiddenCircuits.Complexity.OracleMove

/-! A physically initialized unary loop with a fresh
external clock, followed by actual index reset. -/
namespace HiddenCircuits.Circuit.Runtime.FramedFor
open HiddenCircuits.Complexity OracleBlock HiddenCircuits.DH.Runtime

variable {k : ℕ}
def frame (s : Store k) (clock : BitString) : Store (k+1) := Fin.lastCases clock s
def embedding (k : ℕ) : Fin (k+1) ↪ Fin (k+2) where
  toFun := Fin.castSucc
  inj' := Fin.castSucc_injective _
@[simp] lemma frame_body (s : Store k) (clock : BitString) (i : Fin (k+1)) :
    frame s clock (embedding k i)=s i := by simp [frame,embedding]
@[simp] lemma frame_clock (s : Store k) (clock : BitString) : frame s clock (Fin.last (k+1))=clock := by simp [frame]
lemma body_ne_clock (i : Fin (k+1)) : embedding k i≠Fin.last (k+1) := by
  intro h;have hh:=congrArg Fin.val h;dsimp [embedding] at hh;omega
lemma update_clock (s : Store k) (clock xs : BitString) :
    Function.update (frame s clock) (Fin.last (k+1)) xs=frame s xs := by
  funext i
  refine Fin.lastCases ?_ (fun j=>?_) i
  · simp
  · simp [body_ne_clock,show j.castSucc=embedding k j from rfl]
lemma update_body (s : Store k) (clock xs : BitString) (i : Fin (k+1)) :
    Function.update (frame s clock) (embedding k i) xs=frame (Function.update s i xs) clock := by
  funext j
  refine Fin.lastCases ?_ (fun j=>?_) j
  · simp [Ne.symm (body_ne_clock i)]
  · change Function.update (frame s clock) (embedding k i) xs (embedding k j)=frame (Function.update s i xs) clock (embedding k j)
    simp only [Function.update_apply,(embedding k).injective.eq_iff,frame_body]

lemma lift_executes (B : OracleBlock k) (g : BitString → ℕ) (s t : Store k) (clock : BitString) (c : ℕ)
    (h : B.Executes g s t c) : (rename B (embedding k)).Executes g (frame s clock) (frame t clock) c := by
  apply rename_executes_to _ _ g h
  · funext i;exact frame_body _ _ i
  · funext i;exact frame_body _ _ i
  · intro i
    refine Fin.lastCases ?_ (fun j=>?_) i
    · intro hi;simp
    · intro hi;exact (hi j rfl).elim

noncomputable def program (bound index temp : Fin (k+1)) (hbt : bound≠temp) (B : OracleBlock k) : OracleBlock (k+1) :=
  seq (copyOn (embedding k bound) (Fin.last (k+1)) (embedding k temp)
    (body_ne_clock _) ((embedding k).injective.ne hbt) (Ne.symm (body_ne_clock _)))
    (seq (push (Fin.last (k+1)) true)
      (seq (UnaryFor.program (Fin.last (k+1)) (embedding k index) (rename B (embedding k))) (clear (embedding k index))))

set_option maxHeartbeats 600000 in
theorem program_executes {D : Type*} (bound index temp : Fin (k+1)) (hbt : bound≠temp)
    (B : OracleBlock k) (g : BitString → ℕ) (step : ℕ→D→D) (state : ℕ→D→Store k)
    (Inv : ℕ→D→Prop) (d C : ℕ)
    (hbound : ∀i x,state i x bound=List.replicate d true)
    (hindex : ∀i x,state i x index=List.replicate i true)
    (htemp : ∀i x,state i x temp=[])
    (hinc : ∀i x,Function.update (state i x) index (true::state i x index)=state (i+1) x)
    (hreset : ∀x,Function.update (state (d+1) x) index []=state 0 x)
    (hbody : ∀i x,Inv i x → i<d+1 → ∃c,B.Executes g (state i x) (state i (step i x)) c ∧ c≤C ∧ Inv (i+1) (step i x))
    (x : D) (hx : Inv 0 x) :
    ∃c,(program bound index temp hbt B).Executes g (frame (state 0 x) [])
      (frame (state 0 (UnaryFor.iterate step 0 (d+1) x)) []) c ∧
      c≤(d+1)*(C+5)+6*d+12 ∧ Inv (d+1) (UnaryFor.iterate step 0 (d+1) x) := by
  have hcopy : (copyOn (embedding k bound) (Fin.last (k+1)) (embedding k temp)
      (body_ne_clock _) ((embedding k).injective.ne hbt) (Ne.symm (body_ne_clock _))).Executes g
      (frame (state 0 x) []) (frame (state 0 x) (List.replicate d true)) (5*d+2) := by
    have h:=copyOn_executes g (embedding k bound) (Fin.last (k+1)) (embedding k temp)
      (body_ne_clock _) ((embedding k).injective.ne hbt) (Ne.symm (body_ne_clock _))
      (frame (state 0 x) []) (by simp [htemp])
    simpa only [frame_body,frame_clock,hbound,List.append_nil,update_clock,List.length_replicate] using h
  have hpush : (push (Fin.last (k+1)) true).Executes g (frame (state 0 x) (List.replicate d true))
      (frame (state 0 x) (List.replicate (d+1) true)) 1 := by
    simpa only [frame_clock,update_clock,List.replicate_succ] using
      push_executes g (Fin.last (k+1)) true (frame (state 0 x) (List.replicate d true))
  obtain ⟨c,hc,hcb,hci⟩ := UnaryFor.executes (Fin.last (k+1)) (embedding k index) (rename B (embedding k))
    g step (fun i m x=>frame (state i x) (List.replicate m true)) Inv C (d+1)
    (by intros;simp)
    (by intros;rw [update_clock])
    (by intro i m x;dsimp only;rw [frame_body,update_body,hinc])
    (by intro i m x hi hil;obtain ⟨c,hc,hcb,hci⟩:=hbody i x hi hil;exact ⟨c,lift_executes B g _ _ _ c hc,hcb,hci⟩)
    0 (d+1) x hx (by omega)
  simp only [Nat.zero_add,List.replicate_zero] at hc hci
  have hclear : (clear (embedding k index)).Executes g (frame (state (d+1) (UnaryFor.iterate step 0 (d+1) x)) [])
      (frame (state 0 (UnaryFor.iterate step 0 (d+1) x)) []) (d+2) := by
    have h:=clear_executes g (embedding k index) (frame (state (d+1) (UnaryFor.iterate step 0 (d+1) x)) [])
    simpa only [frame_body,hindex,List.length_replicate,update_body,hreset,show d+1+1=d+2 by omega] using h
  refine ⟨_,seq_executes _ _ g hcopy (seq_executes _ _ g hpush (seq_executes _ _ g hc hclear)),?_,hci⟩
  omega
end HiddenCircuits.Circuit.Runtime.FramedFor
