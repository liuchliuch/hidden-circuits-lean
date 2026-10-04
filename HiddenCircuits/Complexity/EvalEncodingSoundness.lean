import HiddenCircuits.Complexity.PairEncoding
import HiddenCircuits.Complexity.EncodingSoundness

/-! Soundness of every successful raw WordEval and PairEval decode. Successful
validation identifies the original canonical byte string, not an equivalent
re-encoding with unvalidated trailing data. -/
namespace HiddenCircuits.Complexity
open GraphReduction.Runtime GraphReduction.Runtime.WordGraph
set_option maxHeartbeats 1200000

lemma encodeBitList_of_decodeFuel (fuel : ℕ) (xs : BitString) (ys : List BitString)
    (h : decodeBitListFuel fuel xs=some ys) : encodeBitList ys=xs := by
  induction fuel generalizing xs ys with
  | zero => cases xs <;> simp [decodeBitListFuel] at h;subst ys;rfl
  | succ n ih =>
    cases xs with
    | nil => simp [decodeBitListFuel] at h;subst ys;rfl
    | cons b xs =>
      cases b with
      | false => simp [decodeBitListFuel] at h
      | true =>
        cases hu : unpairBits xs with
        | none => simp [decodeBitListFuel,hu] at h
        | some v =>
          rcases v with ⟨z,zs⟩
          cases hd : decodeBitListFuel n zs with
          | none => simp [decodeBitListFuel,hu,hd] at h
          | some tail =>
            simp only [decodeBitListFuel,hu,hd,Option.map_some,Option.some.injEq] at h
            subst ys
            simp only [encodeBitList,ih zs tail hd,pairBits_of_unpair xs z zs hu]
lemma encodeBitList_of_decode (xs : BitString) (ys : List BitString)
    (h : decodeBitList xs=some ys) : encodeBitList ys=xs := encodeBitList_of_decodeFuel _ _ _ h

lemma stateBits_of_decodeState {n q : ℕ} {xs : BitString} {S : State n q}
    (h : decodeState n q xs=some S) : stateBits S=xs := by
  unfold decodeState at h
  split at h
  next hl =>
    dsimp only at h
    split at h
    next hc =>
      cases h
      apply List.ext_getElem (by simp [stateBits,hl])
      intro i hi hj
      simp [stateBits,List.getElem_ofFn]
    next hc => simp at h
  next hl => simp at h

lemma decodeState_isSome_iff (n q : ℕ) (xs : BitString) :
    (decodeState n q xs).isSome ↔ xs.length=n ∧ xs.count true=q := by
  unfold decodeState
  by_cases hl : xs.length=n
  · simp only [dif_pos hl]
    have hc : (Finset.univ.filter (fun i : Fin n=>xs.get ⟨i.val,by simpa [hl] using i.isLt⟩=true)).card=xs.count true := by
      simpa only [List.Vector.get, List.Vector.toList] using Fin.card_filter_univ_eq_vector_get_eq_count true (⟨xs,hl⟩:List.Vector Bool n)
    simp only [hc]
    split_ifs <;> simp_all
  · simp [hl]

lemma kindBits_of_decodeKind {xs : BitString} {k : LetterKind} (h : decodeKind xs=some k) : kindBits k=xs := by
  unfold decodeKind at h
  split at h <;> cases h <;> rfl

lemma letterBits_of_decodeLetter {n : ℕ} {xs : BitString} {l : Letter n}
    (h : decodeLetter n xs=some l) : letterBits l=xs := by
  unfold decodeLetter at h
  cases hu : unpairBits xs with
  | none => simp [hu] at h
  | some v =>
    rcases v with ⟨kb,ib⟩
    simp only [hu] at h
    cases hk : decodeKind kb with
    | none => simp [hk] at h
    | some k =>
      simp only [hk] at h
      split_ifs at h with hi hb
      cases h
      simp only [letterBits]
      rw [kindBits_of_decodeKind hk,←hb]
      exact pairBits_of_unpair _ _ _ hu

lemma letterBits_of_decodeLetters {n : ℕ} (xs : List BitString) (ls : List (Letter n))
    (h : decodeLetters n xs=some ls) : ls.map letterBits=xs := by
  induction xs generalizing ls with
  | nil => simp [decodeLetters] at h;subst ls;rfl
  | cons x xs ih =>
    cases hl : decodeLetter n x with
    | none => simp [decodeLetters,hl] at h
    | some l =>
      cases ht : decodeLetters n xs with
      | none => simp [decodeLetters,hl,ht] at h
      | some tail =>
        simp [decodeLetters,hl,ht] at h
        subst ls
        simp [letterBits_of_decodeLetter hl,ih tail ht]

lemma pairIndexBits_of_decode {p : ℕ} {xs : BitString} {i : Fin (2*p-1)}
    (h : decodePairIndex p xs=some i) : List.replicate i.val true=xs := by
  unfold decodePairIndex at h
  split_ifs at h with hi hb
  cases h
  exact hb.symm

lemma pairAtom_of_decodePairAtom {p : ℕ} {xs : BitString} {P : CutPair p}
    (h : decodePairAtom p xs=some P) : pairAtom P=xs := by
  unfold decodePairAtom at h
  split at h
  next => cases h;rfl
  next tail =>
    cases hi : decodePairIndex p tail with
    | none => simp [hi] at h
    | some i => simp only [hi,Option.map_some,Option.some.injEq] at h;subst P;simp [pairAtom,pairTag,cutCode,pairIndexBits_of_decode hi]
  next tail =>
    cases hi : decodePairIndex p tail with
    | none => simp [hi] at h
    | some i => simp only [hi,Option.map_some,Option.some.injEq] at h;subst P;simp [pairAtom,pairTag,cutCode,pairIndexBits_of_decode hi]
  next tail =>
    cases hi : decodePairIndex p tail with
    | none => simp [hi] at h
    | some i => simp only [hi,Option.map_some,Option.some.injEq] at h;subst P;simp [pairAtom,pairTag,cutCode,pairIndexBits_of_decode hi]
  next tail =>
    cases hi : decodePairIndex p tail with
    | none => simp [hi] at h
    | some i => simp only [hi,Option.map_some,Option.some.injEq] at h;subst P;simp [pairAtom,pairTag,cutCode,pairIndexBits_of_decode hi]
  next => simp at h

lemma pairAtoms_of_decodePairs {p : ℕ} (xs : List BitString) (ps : List (CutPair p))
    (h : decodePairs p xs=some ps) : ps.map pairAtom=xs := by
  induction xs generalizing ps with
  | nil => simp [decodePairs] at h;subst ps;rfl
  | cons x xs ih =>
    cases hl : decodePairAtom p x with
    | none => simp [decodePairs,hl] at h
    | some l =>
      cases ht : decodePairs p xs with
      | none => simp [decodePairs,hl,ht] at h
      | some tail =>
        simp [decodePairs,hl,ht] at h
        subst ps
        simp [pairAtom_of_decodePairAtom hl,ih tail ht]

lemma decodeWordPayload_sound {p : ℕ} {hp : 0<p} {xs : BitString} {w : WordInstance}
    (h : decodeWordPayload p hp xs=some w) :
    w.particles=p ∧ encodeBitList (stateBits w.source::stateBits w.target::w.word.map letterBits)=xs := by
  unfold decodeWordPayload at h
  cases hl : decodeBitList xs with
  | none => simp [hl] at h
  | some fields =>
    cases fields with
    | nil => simp [hl] at h
    | cons source fields =>
      cases fields with
      | nil => simp [hl] at h
      | cons target atoms =>
        cases hs : decodeState (2*p) p source with
        | none => simp [hl,hs] at h
        | some S =>
          cases ht : decodeState (2*p) p target with
          | none => simp [hl,hs,ht] at h
          | some T =>
            cases ha : decodeLetters (2*p) atoms with
            | none => simp [hl,hs,ht,ha] at h
            | some ps =>
              simp only [hl,hs,ht,ha] at h
              cases h
              refine ⟨rfl,?_⟩
              simp only
              rw [stateBits_of_decodeState hs,stateBits_of_decodeState ht,letterBits_of_decodeLetters atoms ps ha]
              exact encodeBitList_of_decode xs _ hl

lemma wordBits_of_decodeWord {xs : BitString} {w : WordInstance}
    (h : decodeWord xs=some w) : wordBits w=xs := by
  unfold decodeWord at h
  cases hu : unpairBits xs with
  | none => simp [hu] at h
  | some v =>
    rcases v with ⟨header,payload⟩
    simp only [hu] at h
    split_ifs at h with hp hb
    obtain ⟨hw,hpayload⟩ := decodeWordPayload_sound h
    unfold wordBits
    rw [hpayload,hw,←hb]
    exact pairBits_of_unpair _ _ _ hu

lemma decodePairPayload_sound {p : ℕ} {hp : 0<p} {xs : BitString} {w : PairInput}
    (h : decodePairPayload p hp xs=some w) :
    w.particles=p ∧ encodeBitList (stateBits w.source::stateBits w.target::w.pairs.map pairAtom)=xs := by
  unfold decodePairPayload at h
  cases hl : decodeBitList xs with
  | none => simp [hl] at h
  | some fields =>
    cases fields with
    | nil => simp [hl] at h
    | cons source fields =>
      cases fields with
      | nil => simp [hl] at h
      | cons target atoms =>
        cases hs : decodeState (2*p) p source with
        | none => simp [hl,hs] at h
        | some S =>
          cases ht : decodeState (2*p) p target with
          | none => simp [hl,hs,ht] at h
          | some T =>
            cases ha : decodePairs p atoms with
            | none => simp [hl,hs,ht,ha] at h
            | some ps =>
              simp only [hl,hs,ht,ha] at h
              split_ifs at h with hn
              cases h
              refine ⟨rfl,?_⟩
              simp only
              rw [stateBits_of_decodeState hs,stateBits_of_decodeState ht,pairAtoms_of_decodePairs atoms ps ha]
              exact encodeBitList_of_decode xs _ hl

lemma pairInputBits_of_decodePairInput {xs : BitString} {w : PairInput}
    (h : decodePairInput xs=some w) : pairInputBits w=xs := by
  unfold decodePairInput at h
  cases hu : unpairBits xs with
  | none => simp [hu] at h
  | some v =>
    rcases v with ⟨header,payload⟩
    simp only [hu] at h
    split_ifs at h with hp hb
    obtain ⟨hw,hpayload⟩ := decodePairPayload_sound h
    unfold pairInputBits
    rw [hpayload,hw,←hb]
    exact pairBits_of_unpair _ _ _ hu
end HiddenCircuits.Complexity
