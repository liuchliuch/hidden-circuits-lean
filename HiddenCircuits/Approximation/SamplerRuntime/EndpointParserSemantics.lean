import HiddenCircuits.Approximation.SamplerRuntime.EndpointParserFinish

/-! Fresh reconstruction of endpoint scan semantics on every raw bit string,
including malformed encodings and the zero-row case. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.EndpointParser
open Complexity GraphReduction MonotoneEndpointEncoding

lemma unary_iff (xs : BitString) : xs.all id=true ↔ xs=List.replicate xs.length true := by
  induction xs with
  | nil => simp
  | cons b xs ih => cases b <;> simp_all [List.replicate_succ]

lemma rows_cons (a : ℕ) {m : ℕ} (f : Fin m → ℕ) :
    rows (Fin.cons a f)=List.replicate a true::rows f := by
  simp [rows,List.ofFn_succ]
lemma rows_split {m : ℕ} (f : Fin (m+1) → ℕ) :
    rows f=List.replicate (f 0) true::rows (fun i => f i.succ) := by
  simp [rows,List.ofFn_succ]

lemma monotone_cons {m : ℕ} (a : ℕ) (f : Fin m → ℕ) (h : Monotone f) (ha : ∀i,a≤f i) : Monotone (Fin.cons a f) := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact le_rfl
    | succ j => exact ha j
  | succ i =>
    cases j using Fin.cases with
    | zero => exact False.elim (by simpa using hij)
    | succ j => exact h (by simpa using hij)

namespace Scan
structure Fits {m : ℕ} (s : State) (lo hi : Fin m → ℕ) : Prop where
  lows_eq : s.lows=encodeBitList (rows lo)
  highs_eq : s.highs=encodeBitList (rows hi)
  lo_mono : Monotone lo
  hi_mono : Monotone hi
  lo_lower : ∀i,s.prevLo.length≤lo i
  hi_lower : ∀i,s.prevHi.length≤hi i
  lo_hi : ∀i,lo i≤hi i
  hi_bound : ∀i,hi i≤s.header.length

theorem accepted_rows (m : ℕ) (s : State) (h : result (run m s)=true) :
    s.valid=true ∧ ∃lo hi : Fin m → ℕ,Fits s lo hi := by
  induction m generalizing s with
  | zero =>
    have hh : s.valid=true ∧ s.lows=[] ∧ s.highs=[] := by
      simpa [run,result,Bool.and_eq_true,and_assoc] using h
    refine ⟨hh.1,fun i => i.elim0,fun i => i.elim0,?_⟩
    constructor
    · simpa [rows] using hh.2.1
    · simpa [rows] using hh.2.2
    all_goals intro i; exact i.elim0
  | succ m ih =>
    obtain ⟨hv,lo,hi,hf⟩ := ih (step s) h
    change rowValid s=true at hv
    simp only [rowValid,Bool.and_eq_true,decide_eq_true_eq,and_assoc] at hv
    rcases hv with ⟨hv,hlo,hhi,ul,uh,pl,ph,lh,hn⟩
    refine ⟨hv,Fin.cons (low s).left.length lo,Fin.cons (high s).left.length hi,?_⟩
    constructor
    · rw [rows_cons,encodeBitList]
      have he := head_reconstruct s.lows hlo
      change s.lows=true::pairBits (low s).left (low s).right at he
      rw [he,(unary_iff _).mp ul]
      simpa only [step,List.length_replicate] using congrArg (fun rest => true::pairBits (List.replicate (low s).left.length true) rest) hf.lows_eq
    · rw [rows_cons,encodeBitList]
      have he := head_reconstruct s.highs hhi
      change s.highs=true::pairBits (high s).left (high s).right at he
      rw [he,(unary_iff _).mp uh]
      simpa only [step,List.length_replicate] using congrArg (fun rest => true::pairBits (List.replicate (high s).left.length true) rest) hf.highs_eq
    · exact monotone_cons _ _ hf.lo_mono hf.lo_lower
    · exact monotone_cons _ _ hf.hi_mono hf.hi_lower
    · intro i; refine Fin.cases pl (fun j => pl.trans (hf.lo_lower j)) i
    · intro i; refine Fin.cases ph (fun j => ph.trans (hf.hi_lower j)) i
    · intro i; exact Fin.cases lh hf.lo_hi i
    · intro i; exact Fin.cases hn hf.hi_bound i

theorem rows_accepted {m : ℕ} (s : State) (lo hi : Fin m → ℕ) (hv : s.valid=true) (hf : Fits s lo hi) :
    result (run m s)=true := by
  induction m generalizing s with
  | zero => simp [run,result,hv,hf.lows_eq,hf.highs_eq,rows,encodeBitList]
  | succ m ih =>
    have hl : low s=⟨List.replicate (lo 0) true,encodeBitList (rows (fun i => lo i.succ)),true⟩ := by
      simp [low,hf.lows_eq,rows_split,encodeBitList]
    have hh : high s=⟨List.replicate (hi 0) true,encodeBitList (rows (fun i => hi i.succ)),true⟩ := by
      simp [high,hf.highs_eq,rows_split,encodeBitList]
    have hv' : (step s).valid=true := by
      simp [step,rowValid,hl,hh,hv,hf.lo_lower 0,hf.hi_lower 0,hf.lo_hi 0,hf.hi_bound 0]
    apply ih (step s) (fun i => lo i.succ) (fun i => hi i.succ) hv'
    constructor
    · simp [step,hl]
    · simp [step,hh]
    · intro i j hij; exact hf.lo_mono (by simpa using hij)
    · intro i j hij; exact hf.hi_mono (by simpa using hij)
    · intro i; simpa [step,hl] using hf.lo_mono (Fin.zero_le i.succ)
    · intro i; simpa [step,hh] using hf.hi_mono (Fin.zero_le i.succ)
    · intro i; exact hf.lo_hi i.succ
    · intro i; exact hf.hi_bound i.succ
end Scan

def initial (xs : BitString) : Scan.State :=
  ⟨(first xs).left,[],[],(second xs).left,(third xs).left,
    (first xs).ok && (second xs).ok && (third xs).ok && (first xs).left.all id && (third xs).right.isEmpty⟩
def valid (xs : BitString) : Bool := Scan.result (Scan.run (first xs).left.length (initial xs))

theorem valid_canonical {xs : BitString} (h : valid xs=true) : ∃E : Input,xs=encode E := by
  obtain ⟨hv,lo,hi,hf⟩ := Scan.accepted_rows (first xs).left.length (initial xs) h
  simp only [initial,Bool.and_eq_true,and_assoc] at hv
  rcases hv with ⟨h₁,h₂,h₃,hu,hr⟩
  let E : Approximation.MonotoneEndpoints (first xs).left.length :=
    ⟨lo,hi,hf.lo_mono,hf.hi_mono,hf.lo_hi,hf.hi_bound⟩
  refine ⟨⟨(first xs).left.length,E⟩,?_⟩
  have a := head_reconstruct xs h₁
  change xs=true::pairBits (first xs).left (first xs).right at a
  have b := head_reconstruct (first xs).right h₂
  have c := head_reconstruct (second xs).right h₃
  change (first xs).right=true::pairBits (second xs).left (second xs).right at b
  change (second xs).right=true::pairBits (third xs).left (third xs).right at c
  have hc : (third xs).right=[] := List.isEmpty_iff.mp hr
  have hl : (second xs).left=encodeBitList (rows lo) := hf.lows_eq
  have hh : (third xs).left=encodeBitList (rows hi) := hf.highs_eq
  have hx : xs=encodeBitList [(first xs).left,(second xs).left,(third xs).left] := by
    calc
      xs=true::pairBits (first xs).left (first xs).right := a
      _=true::pairBits (first xs).left (true::pairBits (second xs).left (true::pairBits (third xs).left [])) := by rw [b,c,hc]
      _=_ := rfl
  calc
    xs=encodeBitList [(first xs).left,(second xs).left,(third xs).left] := hx
    _=encode ⟨(first xs).left.length,E⟩ := by
      change encodeBitList _=encodeBitList [List.replicate (first xs).left.length true,encodeBitList (rows lo),encodeBitList (rows hi)]
      rw [hl,hh]
      exact congrArg (fun z => encodeBitList [z,encodeBitList (rows lo),encodeBitList (rows hi)]) ((unary_iff _).mp hu)

theorem valid_encode (E : Input) : valid (encode E)=true := by
  rcases E with ⟨n,E⟩
  have hi : initial (encode ⟨n,E⟩)=
      ⟨List.replicate n true,[],[],encodeBitList (rows E.lo),encodeBitList (rows E.hi),true⟩ := by
    simp [initial,encode,first,second,third,encodeBitList,headResult]
  have hn : (first (encode ⟨n,E⟩)).left.length=n := by simp [first,encode,encodeBitList,headResult]
  rw [valid,hn,hi]
  apply Scan.rows_accepted _ E.lo E.hi rfl
  constructor
  · rfl
  · rfl
  · exact E.lo_mono
  · exact E.hi_mono
  · intro i; exact Nat.zero_le _
  · intro i; exact Nat.zero_le _
  · exact E.lo_le_hi
  · intro i; simpa using E.hi_le i
end HiddenCircuits.Approximation.SamplerRuntime.EndpointParser
