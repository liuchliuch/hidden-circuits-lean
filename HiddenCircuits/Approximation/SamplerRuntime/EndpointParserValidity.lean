import HiddenCircuits.Approximation.SamplerRuntime.EndpointParserSemantics

/-! Fresh decoder retraction and all-input agreement: malformed representations
are rejected, while every literal endpoint encoding is accepted. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.EndpointParser
open Complexity GraphReduction MonotoneEndpointEncoding GraphVerifier
set_option maxHeartbeats 900000

lemma unpair_reconstruct {xs a b : BitString} (h : unpairBits xs=some (a,b)) : xs=pairBits a b := by
  rw [parse_spec] at h
  cases hp : (parse xs).ok
  · simp [hp] at h
  · simp only [hp,ite_true,Option.some.injEq,Prod.mk.injEq] at h
    rw [←h.1,←h.2]
    exact (parse_reconstruct xs hp).symm

lemma listFuel_reconstruct (fuel : ℕ) (xs : BitString) (ys : List BitString)
    (h : decodeBitListFuel fuel xs=some ys) : xs=encodeBitList ys := by
  induction fuel generalizing xs ys with
  | zero => cases xs <;> simp_all [decodeBitListFuel,encodeBitList]
  | succ fuel ih =>
    cases xs with
    | nil => simp_all [decodeBitListFuel,encodeBitList]
    | cons b xs =>
      cases b with
      | false => simp [decodeBitListFuel] at h
      | true =>
        cases hp : unpairBits xs with
        | none => simp [decodeBitListFuel,hp] at h
        | some pair =>
          rcases pair with ⟨a,rest⟩
          cases hr : decodeBitListFuel fuel rest with
          | none => simp [decodeBitListFuel,hp,hr] at h
          | some tail =>
            simp only [decodeBitListFuel,hp,hr,Option.map_some,Option.some.injEq] at h
            subst ys
            rw [unpair_reconstruct hp,ih rest tail hr]
            rfl
lemma list_reconstruct {xs : BitString} {ys : List BitString} (h : decodeBitList xs=some ys) :
    xs=encodeBitList ys := listFuel_reconstruct xs.length xs ys h

lemma decodeRows_reconstruct {n : ℕ} {xs : List BitString} {f : Fin n → ℕ}
    (h : decodeRows n xs=some f) : xs=rows f := by
  unfold decodeRows at h
  split at h
  next hl =>
    split at h
    next hu =>
      simp only [Option.some.injEq] at h
      subst f
      apply List.ext_get
      · simp [rows,hl]
      · intro i hi hj
        have hii : i<n := by omega
        have hh := hu ⟨i,hii⟩
        simpa [rows,List.get_eq_getElem] using hh
    next => contradiction
  next => contradiction

lemma ofFunctions_fields {n : ℕ} {lo hi : Fin n → ℕ} {E : Approximation.MonotoneEndpoints n}
    (h : ofFunctions lo hi=some E) : lo=E.lo ∧ hi=E.hi := by
  unfold ofFunctions at h
  split at h
  next hp => cases h; exact ⟨rfl,rfl⟩
  next => contradiction

lemma payload_reconstruct {n : ℕ} {ls hs : BitString} {E : Input}
    (h : decodePayload n ls hs=some E) :
    ∃F : Approximation.MonotoneEndpoints n,E=⟨n,F⟩ ∧
      ls=encodeBitList (rows F.lo) ∧ hs=encodeBitList (rows F.hi) := by
  unfold decodePayload at h
  cases hl : decodeBitList ls with
  | none => simp [hl] at h
  | some lows =>
    cases hh : decodeBitList hs with
    | none => simp [hl,hh] at h
    | some highs =>
      simp only [hl,hh] at h
      cases hdl : decodeRows n lows with
      | none => simp [hdl] at h
      | some lo =>
        cases hdh : decodeRows n highs with
        | none => simp [hdl,hdh] at h
        | some hi =>
          simp only [hdl,hdh] at h
          cases hof : ofFunctions lo hi with
          | none => simp [hof] at h
          | some F =>
            simp only [hof,Option.map_some,Option.some.injEq] at h
            obtain ⟨rfl,rfl⟩ := ofFunctions_fields hof
            refine ⟨F,h.symm,?_,?_⟩
            · exact (list_reconstruct hl).trans (congrArg encodeBitList (decodeRows_reconstruct hdl))
            · exact (list_reconstruct hh).trans (congrArg encodeBitList (decodeRows_reconstruct hdh))

theorem decode_reconstruct {xs : BitString} {E : Input} (h : decode xs=some E) : xs=encode E := by
  unfold decode at h
  cases hd : decodeBitList xs with
  | none => simp [hd] at h
  | some fields =>
    simp only [hd] at h
    split at h
    next header ls hs he =>
      split at h
      next hu =>
        obtain ⟨F,rfl,hl,hh⟩ := payload_reconstruct h
        have hx := list_reconstruct hd
        rw [Option.some.inj he,hl,hh] at hx
        exact hx.trans (congrArg (fun w : BitString => encodeBitList [w,encodeBitList (rows F.lo),encodeBitList (rows F.hi)]) hu)
      next => contradiction
    next => contradiction

theorem valid_eq_decode (xs : BitString) : valid xs=(decode xs).isSome := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hv
    obtain ⟨E,rfl⟩ := valid_canonical hv
    simp
  · intro hd
    cases he : decode xs with
    | none => simp [he] at hd
    | some E => rw [decode_reconstruct he]; exact valid_encode E

theorem fields_of_decode {xs : BitString} {E : Input} (h : decode xs=some E) :
    (first xs).left=List.replicate E.1 true ∧
    (second xs).left=encodeBitList (rows E.2.lo) ∧ (third xs).left=encodeBitList (rows E.2.hi) := by
  rw [decode_reconstruct h]
  simp [first,second,third,encode,encodeBitList,headResult]
end HiddenCircuits.Approximation.SamplerRuntime.EndpointParser
