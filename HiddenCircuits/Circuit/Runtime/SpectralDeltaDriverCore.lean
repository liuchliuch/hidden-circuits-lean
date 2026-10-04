import HiddenCircuits.Circuit.Runtime.SourceFrontend
import HiddenCircuits.Circuit.Runtime.SpectralDeltaLoopCore

/-! Four real external registers: two conserved spectral masters and two
clean loop clocks. The 64-register native Delta cell is physically framed. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralDeltaDriver
open Complexity OracleBlock BinaryArithmetic Polynomial SourceFrontend

def frame (low : Store 63) (first second : BitString) : Store 67 :=
  FramedFor.frame (FramedFor.frame (FramedFor.frame (FramedFor.frame low second) []) first) []
def lowEmbedding : Fin 64 ↪ Fin 68 :=
  (FramedFor.embedding 63).trans ((FramedFor.embedding 64).trans
    ((FramedFor.embedding 65).trans (FramedFor.embedding 66)))
def lowPort (i : Fin 64) : Fin 68 := lowEmbedding i
@[simp] lemma lowEmbedding_val (i : Fin 64) : (lowEmbedding i).val=i.val := rfl
def firstPort : Fin 68 := FramedFor.embedding 66 (Fin.last 66)
def secondPort : Fin 68 := FramedFor.embedding 66 (FramedFor.embedding 65 (FramedFor.embedding 64 (Fin.last 64)))

@[simp] lemma frame_low (low : Store 63) (first second : BitString) (i : Fin 64) :
    frame low first second (lowPort i)=low i := by simp [frame,lowPort,lowEmbedding]
@[simp] lemma frame_first (low : Store 63) (first second : BitString) :
    frame low first second firstPort=first := by simp only [frame,firstPort,FramedFor.frame_body,FramedFor.frame_clock]
@[simp] lemma frame_second (low : Store 63) (first second : BitString) :
    frame low first second secondPort=second := by simp only [frame,secondPort,FramedFor.frame_body,FramedFor.frame_clock]
lemma frame_update_low (low : Store 63) (first second xs : BitString) (i : Fin 64) :
    Function.update (frame low first second) (lowPort i) xs=frame (Function.update low i xs) first second := by
  unfold frame lowPort lowEmbedding
  simp only [Function.Embedding.trans_apply]
  rw [FramedFor.update_body,FramedFor.update_body,FramedFor.update_body,FramedFor.update_body]
lemma frame_update_first (low : Store 63) (first second xs : BitString) :
    Function.update (frame low first second) firstPort xs=frame low xs second := by
  unfold frame firstPort
  rw [FramedFor.update_body,FramedFor.update_clock]
lemma frame_update_second (low : Store 63) (first second xs : BitString) :
    Function.update (frame low first second) secondPort xs=frame low first xs := by
  unfold frame secondPort
  rw [FramedFor.update_body,FramedFor.update_body,FramedFor.update_body,FramedFor.update_clock]

lemma frame_length_bound {k : ℕ} (s : Store k) (clock : BitString) (B : ℕ)
    (hs : ∀i,(s i).length≤B) (hc : clock.length≤B) : ∀i,(FramedFor.frame s clock i).length≤B := by
  intro i
  refine Fin.lastCases ?_ (fun j=>?_) i
  · simpa [FramedFor.frame] using hc
  · simpa [FramedFor.frame] using hs j
lemma frame_bound (low : Store 63) (B : ℕ) (hB : ∀i,(low i).length≤B) :
    ∀i,(frame low [] [] i).length≤B := by
  apply frame_length_bound _ _ _
  · apply frame_length_bound _ _ _
    · apply frame_length_bound _ _ _
      · exact frame_length_bound _ _ _ hB (by simp)
      · simp
    · simp
  · simp

lemma frame_empty : frame (fun _ : Fin 64=>([]:BitString)) [] []=(fun _=>[]) := by
  have he {k : ℕ} : FramedFor.frame (fun _ : Fin (k+1)=>([]:BitString)) []=(fun _=>[]) := by
    funext i
    refine Fin.lastCases ?_ (fun j=>?_) i <;> simp [FramedFor.frame]
  simp only [frame,he]
lemma frame_initial (xs : BitString) :
    frame (Function.update (fun _ : Fin 64=>([]:BitString)) 0 xs) [] []=
      Function.update (fun _ : Fin 68=>([]:BitString)) 0 xs := by
  rw [←frame_update_low,frame_empty]
  rfl

noncomputable def lift (B : OracleBlock 63) : OracleBlock 67 :=
  rename (rename (rename (rename B (FramedFor.embedding 63)) (FramedFor.embedding 64))
    (FramedFor.embedding 65)) (FramedFor.embedding 66)
lemma lift_executes (B : OracleBlock 63) (g : BitString → ℕ) (s t : Store 63)
    (first second : BitString) (c : ℕ) (h : B.Executes g s t c) :
    (lift B).Executes g (frame s first second) (frame t first second) c := by
  exact FramedFor.lift_executes _ g _ _ [] c (FramedFor.lift_executes _ g _ _ first c
    (FramedFor.lift_executes _ g _ _ [] c (FramedFor.lift_executes _ g _ _ second c h)))

lemma low_ne_first (i : Fin 64) : lowPort i≠firstPort := by
  intro h;have hv:=congrArg Fin.val h;dsimp [lowPort,lowEmbedding,firstPort,FramedFor.embedding] at hv;omega
lemma low_ne_second (i : Fin 64) : lowPort i≠secondPort := by
  intro h;have hv:=congrArg Fin.val h;dsimp [lowPort,lowEmbedding,secondPort,FramedFor.embedding] at hv;omega

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

noncomputable def firstLoad : OracleBlock 67 := dropMove (lowPort 58) firstPort (lowPort 24)
  (low_ne_first _) (lowEmbedding.injective.ne (by decide)) (Ne.symm (low_ne_first _))
noncomputable def secondLoad : OracleBlock 67 := dropMove (lowPort 59) secondPort (lowPort 24)
  (low_ne_second _) (lowEmbedding.injective.ne (by decide)) (Ne.symm (low_ne_second _))
noncomputable def front : OracleBlock 67 := seq (lift SourceFrontend.program) (seq firstLoad secondLoad)
noncomputable def frontTime : Polynomial ℕ := SourceFrontend.time+12*(X+SourceFrontend.time)+18

set_option maxHeartbeats 600000 in
theorem front_frame_executes (g : BitString→ℕ) {n : ℕ} (w : List (ConstraintGate n))
    (wire : BitString) (B : ℕ) (hB : ∀i,(rawStore w 0 wire i).length≤B) :
    ∃c,front.Executes g (frame (rawStore w 0 wire) [] [])
      (frame (SourceSample.store (SourceSample.canonical w 0 0 0 0) {accumulator:=(0,1)})
        (List.replicate (Fintype.card (SpectralIndex (forbidOccurrences w))-1) true)
        (List.replicate (Fintype.card (SpectralIndex (signOccurrences w))-1) true)) c ∧ c≤frontTime.eval B := by
  let low:=SourceSample.store (SourceSample.canonical w 0 0 0 0) {accumulator:=(0,1)}
  let f:=Fintype.card (SpectralIndex (forbidOccurrences w))
  let z:=Fintype.card (SpectralIndex (signOccurrences w))
  have hf : 0<f := spectralIndex_card_pos _
  have hz : 0<z := spectralIndex_card_pos _
  obtain ⟨c,hc,hcb⟩:=SourceFrontend.program_executes g w 0 wire B hB
  have hwide:=lift_executes SourceFrontend.program g _ _ [] [] c hc
  have hfirst : firstLoad.Executes g (frame (initializedStore w 0) [] [])
      (frame (Function.update low 59 (List.replicate z true)) (List.replicate (f-1) true) []) (6*(f-1)+7) := by
    have h:=dropMove_executes (lowPort 58) firstPort (lowPort 24)
      (low_ne_first _) (lowEmbedding.injective.ne (by decide)) (Ne.symm (low_ne_first _))
      g (frame (initializedStore w 0) [] []) f hf (by rw [frame_low];rfl) (by simp) (by rw [frame_low];rfl)
    rw [frame_update_first,frame_update_low] at h
    have he : Function.update (initializedStore w 0) (58:Fin 64) []=Function.update low 59 (List.replicate z true) := by
      funext i;fin_cases i <;> rfl
    rw [he] at h
    exact h
  have hsecond : secondLoad.Executes g
      (frame (Function.update low 59 (List.replicate z true)) (List.replicate (f-1) true) [])
      (frame low (List.replicate (f-1) true) (List.replicate (z-1) true)) (6*(z-1)+7) := by
    have h:=dropMove_executes (lowPort 59) secondPort (lowPort 24)
      (low_ne_second _) (lowEmbedding.injective.ne (by decide)) (Ne.symm (low_ne_second _))
      g (frame (Function.update low 59 (List.replicate z true)) (List.replicate (f-1) true) []) z hz
      (by rw [frame_low];simp) (by simp) (by rw [frame_low];rfl)
    rw [frame_update_second,frame_update_low] at h
    have he : Function.update (Function.update low (59:Fin 64) (List.replicate z true)) 59 []=low := by
      funext i;fin_cases i <;> rfl
    rw [he] at h
    exact h
  have hb:=hc.stack_bound hB
  change ∀i : Fin 64,(initializedStore w 0 i).length≤B+c at hb
  have hfb : f≤B+c := by simpa [initializedStore,f] using hb (58:Fin 64)
  have hzb : z≤B+c := by simpa [initializedStore,z] using hb (59:Fin 64)
  refine ⟨_,seq_executes _ _ g hwide (seq_executes _ _ g hfirst hsecond),?_⟩
  simp only [frontTime,eval_add,eval_mul,eval_X,eval_ofNat]
  omega
end HiddenCircuits.Circuit.Runtime.SpectralDeltaDriver
