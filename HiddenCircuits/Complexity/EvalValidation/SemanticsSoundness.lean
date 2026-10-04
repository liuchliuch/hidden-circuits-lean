import HiddenCircuits.Complexity.EvalValidation.Semantics

/-! The Boolean physical validator recognizes exactly the existing decoders,
including every malformed input and the nonempty-pair condition. -/
namespace HiddenCircuits.Complexity.EvalValidation.Semantics
open GraphVerifier GraphReduction.Runtime GraphReduction.Runtime.WordGraph
set_option maxHeartbeats 1200000

lemma field_reconstruct (xs : BitString) (h : Field.valid xs=true) :
    true::pairBits (Field.item xs).left (Field.item xs).right=xs := by
  cases xs with
  | nil => simp [Field.valid,Field.item,Field.marker,parse] at h
  | cons b bs =>
    cases b with
    | false => simp [Field.valid,Field.marker] at h
    | true =>
      have hok : (parse bs).ok=true := by simpa [Field.valid,Field.item,Field.marker] using h
      apply congrArg (List.cons true)
      apply pairBits_of_unpair
      rw [parse_spec,hok]
      rfl
lemma marker_positive (xs : BitString) (h : Field.marker xs=true) : 0<xs.length := by
  cases xs with
  | nil => simp [Field.marker] at h
  | cons b bs => simp

lemma validList_pair_witness (p : ℕ) (width xs : BitString) (hw : width.length=2*p)
    (h : validList true width xs=true) : ∃ps : List (CutPair p),encodeBitList (ps.map pairAtom)=xs := by
  induction xs using (measure List.length).wf.induction with
  | h xs ih =>
    cases xs with
    | nil => exact ⟨[],rfl⟩
    | cons b bs =>
      rw [validList] at h
      simp only [Bool.and_eq_true] at h
      have ho : (parse bs).ok=true := by aesop
      have hb : b=true := by aesop
      have ha : atomValid true width (parse bs).left=true := by aesop
      have ht : validList true width (parse bs).right=true := by aesop
      subst b
      obtain ⟨ps,hps⟩ := ih (parse bs).right (Field.tail_shorter true bs) ht
      have hd : (decodePairAtom p (parse bs).left).isSome=true := by
        simpa only [atomValid,if_true,PairAtom.valid_decode p _ width hw] using ha
      cases hp : decodePairAtom p (parse bs).left with
      | none => simp [hp] at hd
      | some P =>
        refine ⟨P::ps,?_⟩
        simp only [List.map_cons,encodeBitList,hps,pairAtom_of_decodePairAtom hp]
        apply congrArg (List.cons true)
        apply pairBits_of_unpair
        rw [parse_spec,ho]
        rfl

lemma validList_word_witness (p : ℕ) (width xs : BitString) (hw : width.length=2*p)
    (h : validList false width xs=true) : ∃ls : List (Letter (2*p)),encodeBitList (ls.map letterBits)=xs := by
  induction xs using (measure List.length).wf.induction with
  | h xs ih =>
    cases xs with
    | nil => exact ⟨[],rfl⟩
    | cons b bs =>
      rw [validList] at h
      simp only [Bool.and_eq_true] at h
      have ho : (parse bs).ok=true := by aesop
      have hb : b=true := by aesop
      have ha : atomValid false width (parse bs).left=true := by aesop
      have ht : validList false width (parse bs).right=true := by aesop
      subst b
      obtain ⟨ls,hls⟩ := ih (parse bs).right (Field.tail_shorter true bs) ht
      have hd : (decodeLetter (2*p) (parse bs).left).isSome=true := by
        simpa only [atomValid,if_false,WordAtom.valid_decode p _ width hw] using ha
      cases hp : decodeLetter (2*p) (parse bs).left with
      | none => simp [hp] at hd
      | some l =>
        refine ⟨l::ls,?_⟩
        simp only [List.map_cons,encodeBitList,hls,letterBits_of_decodeLetter hp]
        apply congrArg (List.cons true)
        apply pairBits_of_unpair
        rw [parse_spec,ho]
        rfl

lemma validList_pair_encode (p : ℕ) (width : BitString) (hw : width.length=2*p) (ps : List (CutPair p)) :
    validList true width (encodeBitList (ps.map pairAtom))=true := by
  induction ps with
  | nil => simp [encodeBitList,validList]
  | cons P ps ih =>
    simp [List.map_cons,encodeBitList,validList,parse_pair,atomValid,PairAtom.valid_decode p _ width hw,ih]
lemma validList_word_encode (p : ℕ) (width : BitString) (hw : width.length=2*p) (ls : List (Letter (2*p))) :
    validList false width (encodeBitList (ls.map letterBits))=true := by
  induction ls with
  | nil => simp [encodeBitList,validList]
  | cons l ls ih =>
    simp [List.map_cons,encodeBitList,validList,parse_pair,atomValid,WordAtom.valid_decode p _ width hw,ih]

lemma test_components (mode : Bool) (xs : BitString) : test mode xs=true ↔
    validList mode (width xs) (second xs).right=true ∧ nonemptyFlag mode (second xs).right=true ∧
    Mask.valid (second xs).left (header xs) (width xs)=true ∧ Field.valid (first xs).right=true ∧
    Mask.valid (first xs).left (header xs) (width xs)=true ∧ Field.valid (parse xs).right=true ∧
    Field.marker (header xs)=true ∧ (header xs).all id=true ∧ (parse xs).ok=true := by
  simp [test,beforeFlags,parsedFlags,headerFlags,Bool.and_assoc]

lemma test_pair_sound (xs : BitString) (h : test true xs=true) : (decodePairInput xs).isSome=true := by
  obtain ⟨hl,hn,hT,hfT,hS,hfS,hpos,hall,ho⟩ := (test_components true xs).mp h
  let p := (header xs).length
  have hp : 0<p := marker_positive _ hpos
  have hw : (width xs).length=2*p := by simp [width,p];omega
  have hu : header xs=List.replicate p true := (GraphVerifier.header_all_true _).mp hall
  have hs : (decodeState (2*p) p (first xs).left).isSome := by
    apply (decodeState_isSome_iff _ _ _).mpr
    have hm := hS
    simp only [Mask.valid,Bool.and_eq_true,decide_eq_true_eq] at hm
    exact ⟨hm.2.trans hw,hm.1⟩
  have ht : (decodeState (2*p) p (second xs).left).isSome := by
    apply (decodeState_isSome_iff _ _ _).mpr
    have hm := hT
    simp only [Mask.valid,Bool.and_eq_true,decide_eq_true_eq] at hm
    exact ⟨hm.2.trans hw,hm.1⟩
  cases hsd : decodeState (2*p) p (first xs).left with
  | none => simp [hsd] at hs
  | some S =>
    cases htd : decodeState (2*p) p (second xs).left with
    | none => simp [htd] at ht
    | some T =>
      obtain ⟨ps,hps⟩ := validList_pair_witness p (width xs) (second xs).right hw hl
      have hne : ps≠[] := by
        intro he
        subst ps
        have hempty : (second xs).right=[] := hps.symm
        simp [nonemptyFlag,hempty] at hn
      let w : PairInput := ⟨p,hp,S,T,ps,hne⟩
      have hbytes : pairInputBits w=xs := by
        unfold pairInputBits
        simp only [w]
        rw [stateBits_of_decodeState hsd,stateBits_of_decodeState htd]
        change pairBits (List.replicate p true) (true::pairBits (first xs).left (true::pairBits (second xs).left (encodeBitList (ps.map pairAtom))))=xs
        rw [hps]
        have hf2 := field_reconstruct (first xs).right hfT
        change true::pairBits (second xs).left (second xs).right=(first xs).right at hf2
        rw [hf2]
        have hf1 := field_reconstruct (parse xs).right hfS
        change true::pairBits (first xs).left (first xs).right=(parse xs).right at hf1
        rw [hf1,←hu]
        exact pairBits_of_unpair _ _ _ (by rw [parse_spec,ho];rfl)
      rw [←hbytes,decodePairInput_pairInputBits]
      rfl

lemma test_word_sound (xs : BitString) (h : test false xs=true) : (decodeWord xs).isSome=true := by
  obtain ⟨hl,hn,hT,hfT,hS,hfS,hpos,hall,ho⟩ := (test_components false xs).mp h
  let p := (header xs).length
  have hp : 0<p := marker_positive _ hpos
  have hw : (width xs).length=2*p := by simp [width,p];omega
  have hu : header xs=List.replicate p true := (GraphVerifier.header_all_true _).mp hall
  have hs : (decodeState (2*p) p (first xs).left).isSome := by
    apply (decodeState_isSome_iff _ _ _).mpr
    have hm := hS
    simp only [Mask.valid,Bool.and_eq_true,decide_eq_true_eq] at hm
    exact ⟨hm.2.trans hw,hm.1⟩
  have ht : (decodeState (2*p) p (second xs).left).isSome := by
    apply (decodeState_isSome_iff _ _ _).mpr
    have hm := hT
    simp only [Mask.valid,Bool.and_eq_true,decide_eq_true_eq] at hm
    exact ⟨hm.2.trans hw,hm.1⟩
  cases hsd : decodeState (2*p) p (first xs).left with
  | none => simp [hsd] at hs
  | some S =>
    cases htd : decodeState (2*p) p (second xs).left with
    | none => simp [htd] at ht
    | some T =>
      obtain ⟨ls,hls⟩ := validList_word_witness p (width xs) (second xs).right hw hl
      let w : WordInstance := ⟨p,hp,S,T,ls⟩
      have hbytes : wordBits w=xs := by
        unfold wordBits
        simp only [w]
        rw [stateBits_of_decodeState hsd,stateBits_of_decodeState htd]
        change pairBits (List.replicate p true) (true::pairBits (first xs).left (true::pairBits (second xs).left (encodeBitList (ls.map letterBits))))=xs
        rw [hls]
        have hf2 := field_reconstruct (first xs).right hfT
        change true::pairBits (second xs).left (second xs).right=(first xs).right at hf2
        rw [hf2]
        have hf1 := field_reconstruct (parse xs).right hfS
        change true::pairBits (first xs).left (first xs).right=(parse xs).right at hf1
        rw [hf1,←hu]
        exact pairBits_of_unpair _ _ _ (by rw [parse_spec,ho];rfl)
      rw [←hbytes,decodeWord_wordBits]
      rfl

lemma mask_encode {p : ℕ} (S : State (2*p) p) :
    Mask.valid (stateBits S) (List.replicate p true) (List.replicate p true++List.replicate p true)=true := by
  have hd : (decodeState (2*p) p (stateBits S)).isSome := by rw [decodeState_stateBits];rfl
  have hc := (decodeState_isSome_iff (2*p) p (stateBits S)).mp hd
  simp [Mask.valid,hc.2,two_mul]
lemma marker_replicate {p : ℕ} (hp : 0<p) : Field.marker (List.replicate p true)=true := by
  cases p with
  | zero => omega
  | succ p => simp [Field.marker,List.replicate_succ]

lemma test_pair_encode (w : PairInput) : test true (pairInputBits w)=true := by
  have hl := validList_pair_encode w.particles (List.replicate w.particles true++List.replicate w.particles true)
    (by simp [two_mul]) w.pairs
  have hn : (encodeBitList (w.pairs.map pairAtom)).isEmpty=false := by
    cases hp : w.pairs with
    | nil => exact (w.nonempty hp).elim
    | cons p ps => rfl
  have hS := mask_encode w.source
  have hT := mask_encode w.target
  have hM := marker_replicate w.positive
  change (List.replicate w.particles true).head?.getD false=true at hM
  simp only [←List.replicate_add] at hl hS hT
  simp [test,beforeFlags,parsedFlags,headerFlags,nonemptyFlag,header,width,first,second,pairInputBits,
    Field.item,Field.valid,Field.marker,parse_pair,encodeBitList,hS,hT,hM,hl,hn]
lemma test_word_encode (w : WordInstance) : test false (wordBits w)=true := by
  have hl := validList_word_encode w.particles (List.replicate w.particles true++List.replicate w.particles true)
    (by simp [two_mul]) w.word
  have hS := mask_encode w.source
  have hT := mask_encode w.target
  have hM := marker_replicate w.positive
  change (List.replicate w.particles true).head?.getD false=true at hM
  simp only [←List.replicate_add] at hl hS hT
  simp [test,beforeFlags,parsedFlags,headerFlags,nonemptyFlag,header,width,first,second,wordBits,
    Field.item,Field.valid,Field.marker,parse_pair,encodeBitList,hS,hT,hM,hl]

theorem test_pair_decode (xs : BitString) : test true xs=(decodePairInput xs).isSome := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact test_pair_sound xs
  · intro h
    cases hd : decodePairInput xs with
    | none => simp [hd] at h
    | some w => rw [←pairInputBits_of_decodePairInput hd];exact test_pair_encode w

theorem test_word_decode (xs : BitString) : test false xs=(decodeWord xs).isSome := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact test_word_sound xs
  · intro h
    cases hd : decodeWord xs with
    | none => simp [hd] at h
    | some w => rw [←wordBits_of_decodeWord hd];exact test_word_encode w
end HiddenCircuits.Complexity.EvalValidation.Semantics
