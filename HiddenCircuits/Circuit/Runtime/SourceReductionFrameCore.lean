import HiddenCircuits.Circuit.Runtime.SourceFrontend
import HiddenCircuits.Circuit.Runtime.SourceWordCall
import HiddenCircuits.Circuit.Runtime.FramedFor
import HiddenCircuits.Circuit.Runtime.SourceFinalization
import HiddenCircuits.Circuit.Runtime.SourceZero

/-! Preserve the complete solver bank and five
external loop registers while the actual source frontend runs. -/
namespace HiddenCircuits.Circuit.Runtime.SourceReduction
open HiddenCircuits.Complexity OracleBlock BinaryArithmetic Polynomial SourceFrontend

def frame (k : ℕ) (low : Store 63) (first second : BitString) : Store (k+69) :=
  FramedFor.frame (FramedFor.frame (FramedFor.frame (FramedFor.frame
    (FramedFor.frame (SourceWordCall.lifted (k:=k) low) []) second) []) first) []
def lowEmbedding (k : ℕ) : Fin 64 ↪ Fin (k+70) :=
  (SourceWordCall.lowEmbedding k).trans ((FramedFor.embedding (k+64)).trans
    ((FramedFor.embedding (k+65)).trans ((FramedFor.embedding (k+66)).trans
      ((FramedFor.embedding (k+67)).trans (FramedFor.embedding (k+68))))))
def lowPort (k : ℕ) (i : Fin 64) : Fin (k+70) := lowEmbedding k i
@[simp] lemma lowEmbedding_val (k : ℕ) (i : Fin 64) : ((lowEmbedding k) i).val=i.val := rfl
def firstPort (k : ℕ) : Fin (k+70) := FramedFor.embedding (k+68) (Fin.last (k+68))
def secondPort (k : ℕ) : Fin (k+70) := FramedFor.embedding (k+68)
  (FramedFor.embedding (k+67) (FramedFor.embedding (k+66) (Fin.last (k+66))))

@[simp] lemma frame_low (k : ℕ) (low : Store 63) (first second : BitString) (i : Fin 64) :
    frame k low first second (lowPort k i)=low i := by
  simp [frame,lowPort,lowEmbedding,SourceWordCall.lifted]
@[simp] lemma frame_first (k : ℕ) (low : Store 63) (first second : BitString) :
    frame k low first second (firstPort k)=first := by simp [frame,firstPort]
@[simp] lemma frame_second (k : ℕ) (low : Store 63) (first second : BitString) :
    frame k low first second (secondPort k)=second := by simp [frame,secondPort]
lemma frame_update_low (k : ℕ) (low : Store 63) (first second xs : BitString) (i : Fin 64) :
    Function.update (frame k low first second) (lowPort k i) xs=frame k (Function.update low i xs) first second := by
  unfold frame lowPort lowEmbedding SourceWordCall.lifted
  simp only [Function.Embedding.trans_apply]
  rw [FramedFor.update_body,FramedFor.update_body,FramedFor.update_body,FramedFor.update_body,
    FramedFor.update_body,SourceWordCall.update_low]
lemma frame_update_first (k : ℕ) (low : Store 63) (first second xs : BitString) :
    Function.update (frame k low first second) (firstPort k) xs=frame k low xs second := by
  unfold frame firstPort
  rw [FramedFor.update_body,FramedFor.update_clock]
lemma frame_update_second (k : ℕ) (low : Store 63) (first second xs : BitString) :
    Function.update (frame k low first second) (secondPort k) xs=frame k low first xs := by
  unfold frame secondPort
  rw [FramedFor.update_body,FramedFor.update_body,FramedFor.update_body,FramedFor.update_clock]

lemma FramedFor.frame_length_bound {k : ℕ} (s : Store k) (clock : BitString) (B : ℕ)
    (hs : ∀i,(s i).length≤B) (hc : clock.length≤B) : ∀i,(FramedFor.frame s clock i).length≤B := by
  intro i
  refine Fin.lastCases ?_ (fun j=>?_) i
  · simpa [FramedFor.frame] using hc
  · simpa [FramedFor.frame] using hs j
lemma frame_bound (k : ℕ) (low : Store 63) (B : ℕ) (hB : ∀i,(low i).length≤B) :
    ∀i,(frame k low [] [] i).length≤B := by
  have hl : ∀i,(SourceWordCall.lifted (k:=k) low i).length≤B := by
    intro i
    unfold SourceWordCall.lifted SourceWordCall.store
    split_ifs with hi
    · exact hB _
    · simp
  apply FramedFor.frame_length_bound _ _ _
  · apply FramedFor.frame_length_bound _ _ _
    · apply FramedFor.frame_length_bound _ _ _
      · apply FramedFor.frame_length_bound _ _ _
        · exact FramedFor.frame_length_bound _ _ _ hl (by simp)
        · simp
      · simp
    · simp
  · simp

lemma FramedFor.frame_empty {k : ℕ} : FramedFor.frame (fun _ : Fin (k+1)=>([]:BitString)) []=(fun _=>[]) := by
  funext i
  refine Fin.lastCases ?_ (fun j=>?_) i <;> simp [FramedFor.frame]
lemma frame_empty (k : ℕ) : frame k (fun _=>([]:BitString)) [] []=(fun _=>[]) := by
  have hl : SourceWordCall.lifted (k:=k) (fun _=>([]:BitString))=(fun _=>[]) := by
    funext i;simp [SourceWordCall.lifted,SourceWordCall.store]
  simp only [frame,hl,FramedFor.frame_empty]
lemma frame_initial (k : ℕ) (xs : BitString) :
    frame k (Function.update (fun _ : Fin 64=>([]:BitString)) 0 xs) [] []=
      Function.update (fun _ : Fin (k+70)=>([]:BitString)) 0 xs := by
  rw [←frame_update_low,frame_empty]
  rfl

noncomputable def lift (k : ℕ) (B : OracleBlock 63) : OracleBlock (k+69) :=
  rename (rename (rename (rename (rename (rename B (SourceWordCall.lowEmbedding k))
    (FramedFor.embedding (k+64))) (FramedFor.embedding (k+65))) (FramedFor.embedding (k+66)))
      (FramedFor.embedding (k+67))) (FramedFor.embedding (k+68))
lemma lift_executes (k : ℕ) (B : OracleBlock 63) (g : BitString → ℕ) (s t : Store 63)
    (first second : BitString) (c : ℕ) (h : B.Executes g s t c) :
    (lift k B).Executes g (frame k s first second) (frame k t first second) c := by
  exact FramedFor.lift_executes _ g _ _ [] c (FramedFor.lift_executes _ g _ _ first c
    (FramedFor.lift_executes _ g _ _ [] c (FramedFor.lift_executes _ g _ _ second c
      (FramedFor.lift_executes _ g _ _ [] c (SourceWordCall.lift_executes _ g _ _ c h)))))

lemma low_ne_first (k : ℕ) (i : Fin 64) : lowPort k i≠firstPort k := by
  intro h;have hv:=congrArg Fin.val h;dsimp [lowPort,lowEmbedding,firstPort,FramedFor.embedding,SourceWordCall.lowEmbedding] at hv;omega
lemma low_ne_second (k : ℕ) (i : Fin 64) : lowPort k i≠secondPort k := by
  intro h;have hv:=congrArg Fin.val h;dsimp [lowPort,lowEmbedding,secondPort,FramedFor.embedding,SourceWordCall.lowEmbedding] at hv;omega

noncomputable def dropMove {k : ℕ} (src dst tmp : Fin (k+1))
    (hsd : src≠dst) (hst : src≠tmp) (hdt : dst≠tmp) : OracleBlock k :=
  branchPop src skip (moveOn src dst tmp hsd hst hdt) (moveOn src dst tmp hsd hst hdt)
lemma dropMove_executes {k : ℕ} (src dst tmp : Fin (k+1))
    (hsd : src≠dst) (hst : src≠tmp) (hdt : dst≠tmp) (g : BitString→ℕ) (s : Store k) (J : ℕ)
    (hJ : 0<J) (hs : s src=List.replicate J true) (hd : s dst=[]) (ht : s tmp=[]) :
    (dropMove src dst tmp hsd hst hdt).Executes g s
      (Function.update (Function.update s dst (List.replicate (J-1) true)) src []) (6*(J-1)+7) := by
  have hj : J=(J-1)+1 := by omega
  have hh : s src=true::List.replicate (J-1) true := by rw [hs];conv_lhs => rw [hj,List.replicate_succ]
  have hm:=moveOn_executes g src dst tmp hsd hst hdt (Function.update s src (List.replicate (J-1) true))
    (by simpa only [Function.update_of_ne hst.symm] using ht)
  simp only [Function.update_self,Function.update_of_ne hsd.symm,hd,List.append_nil,List.length_replicate] at hm
  have he : Function.update (Function.update (Function.update s src (List.replicate (J-1) true)) dst
      (List.replicate (J-1) true)) src []=Function.update (Function.update s dst (List.replicate (J-1) true)) src [] := by
    funext i;simp only [Function.update_apply];split_ifs <;> rfl
  rw [he] at hm
  exact branchPop_true src skip _ _ g hh hm

noncomputable def firstLoad (k : ℕ) : OracleBlock (k+69) := dropMove (lowPort k 58) (firstPort k) (lowPort k 24)
  (low_ne_first _ _) ((lowEmbedding k).injective.ne (by decide)) (Ne.symm (low_ne_first _ _))
noncomputable def secondLoad (k : ℕ) : OracleBlock (k+69) := dropMove (lowPort k 59) (secondPort k) (lowPort k 24)
  (low_ne_second _ _) ((lowEmbedding k).injective.ne (by decide)) (Ne.symm (low_ne_second _ _))
noncomputable def front (k : ℕ) : OracleBlock (k+69) := seq (lift k SourceFrontend.program) (seq (firstLoad k) (secondLoad k))
noncomputable def frontTime : Polynomial ℕ := SourceFrontend.time+12*(X+SourceFrontend.time)+18

set_option maxHeartbeats 600000 in
theorem front_frame_executes (k : ℕ) (g : BitString→ℕ) {n : ℕ} (w : List (ConstraintGate n)) (a : ℕ)
    (wire : BitString) (B : ℕ) (hB : ∀i,(rawStore w a wire i).length≤B) :
    ∃c,(front k).Executes g (frame k (rawStore w a wire) [] [])
      (frame k (SourceSample.store (SourceSample.canonical w a 0 0 0) {accumulator:=(0,1)})
        (List.replicate (Fintype.card (SpectralIndex (forbidOccurrences w))-1) true)
        (List.replicate (Fintype.card (SpectralIndex (signOccurrences w))-1) true)) c ∧ c≤frontTime.eval B := by
  let low:=SourceSample.store (SourceSample.canonical w a 0 0 0) {accumulator:=(0,1)}
  let f:=Fintype.card (SpectralIndex (forbidOccurrences w))
  let z:=Fintype.card (SpectralIndex (signOccurrences w))
  have hf : 0<f := spectralIndex_card_pos _
  have hz : 0<z := spectralIndex_card_pos _
  obtain ⟨c,hc,hcb⟩:=SourceFrontend.program_executes g w a wire B hB
  have hwide:=lift_executes k SourceFrontend.program g _ _ [] [] c hc
  have hfirst : (firstLoad k).Executes g (frame k (initializedStore w a) [] [])
      (frame k (Function.update low 59 (List.replicate z true)) (List.replicate (f-1) true) []) (6*(f-1)+7) := by
    have h:=dropMove_executes (lowPort k 58) (firstPort k) (lowPort k 24)
      (low_ne_first _ _) ((lowEmbedding k).injective.ne (by decide)) (Ne.symm (low_ne_first _ _))
      g (frame k (initializedStore w a) [] []) f hf (by rw [frame_low];rfl) (by simp) (by rw [frame_low];rfl)
    rw [frame_update_first,frame_update_low] at h
    have he : Function.update (initializedStore w a) (58:Fin 64) []=Function.update low 59 (List.replicate z true) := by
      funext i;fin_cases i <;> rfl
    rw [he] at h
    exact h
  have hsecond : (secondLoad k).Executes g
      (frame k (Function.update low 59 (List.replicate z true)) (List.replicate (f-1) true) [])
      (frame k low (List.replicate (f-1) true) (List.replicate (z-1) true)) (6*(z-1)+7) := by
    have h:=dropMove_executes (lowPort k 59) (secondPort k) (lowPort k 24)
      (low_ne_second _ _) ((lowEmbedding k).injective.ne (by decide)) (Ne.symm (low_ne_second _ _))
      g (frame k (Function.update low 59 (List.replicate z true)) (List.replicate (f-1) true) []) z hz
      (by rw [frame_low];simp) (by simp) (by rw [frame_low];rfl)
    rw [frame_update_second,frame_update_low] at h
    have he : Function.update (Function.update low (59:Fin 64) (List.replicate z true)) 59 []=low := by
      funext i;fin_cases i <;> rfl
    rw [he] at h
    exact h
  have hb:=hc.stack_bound hB
  change ∀i : Fin 64,(initializedStore w a i).length≤B+c at hb
  have hfb : f≤B+c := by simpa [initializedStore,f] using hb (58:Fin 64)
  have hzb : z≤B+c := by simpa [initializedStore,z] using hb (59:Fin 64)
  refine ⟨_,seq_executes _ _ g hwide (seq_executes _ _ g hfirst hsecond),?_⟩
  simp only [frontTime,eval_add,eval_mul,eval_X,eval_ofNat]
  omega
end HiddenCircuits.Circuit.Runtime.SourceReduction
