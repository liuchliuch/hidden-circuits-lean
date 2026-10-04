import HiddenCircuits.Complexity.TM2LocalNetwork
import HiddenCircuits.Complexity.InitialNetworkCNF

/-! Construct the verifier's Boolean initial row from constants and individual
certificate bits, retaining each certificate exactly once. -/
namespace HiddenCircuits.Complexity
namespace InputSource
variable {p : ℕ}

def unary (i : Fin p) (f : Bool → Bool) : InputSource p :=
  if f false = f true then .constant (f false) else .bit i (f false)

theorem unary_evaluate (i : Fin p) (f : Bool → Bool) (w : Fin p → Bool) :
    (unary i f).evaluate w = f (w i) := by
  cases hf : f false <;> cases ht : f true <;> cases hw : w i <;>
    simp [unary,evaluate,hf,ht,hw]

def map (f : Bool → Bool) : InputSource p → InputSource p
  | .constant b => .constant (f b)
  | .bit i negate => unary i (fun b => f (Bool.xor b negate))

@[simp] theorem map_evaluate (f : Bool → Bool) (s : InputSource p) (w : Fin p → Bool) :
    (s.map f).evaluate w = f (s.evaluate w) := by
  cases s with
  | constant b => rfl
  | bit i negate => exact unary_evaluate i (fun b => f (Bool.xor b negate)) w
end InputSource

lemma pairBits_append (x y : BitString) : pairBits x y = pairBits x [] ++ y := by
  induction x with
  | nil => rfl
  | cons b x ih => simpa [pairBits] using congrArg (List.cons true ∘ List.cons b) ih

def certificateSources (x : BitString) (m : ℕ) : List (InputSource m) :=
  (pairBits x []).map InputSource.constant ++ List.ofFn (fun i : Fin m => InputSource.bit i false)

theorem certificateSources_evaluate (x : BitString) (m : ℕ) (w : Fin m → Bool) :
    (certificateSources x m).map (fun s => s.evaluate w) = pairBits x (List.ofFn w) := by
  rw [pairBits_append]
  simp [certificateSources,InputSource.evaluate,Function.comp_def]

@[simp] theorem certificateSources_length (x : BitString) (m : ℕ) :
    (certificateSources x m).length = 2*x.length+m+1 := by
  simp [certificateSources]
  omega

namespace VerifierTableau
open TM2BooleanEncoding
variable {v : BitString → Bool}
variable (M : Turing.TM2ComputableInPolyTime id Computability.encodeBool v)
attribute [local instance] Classical.propDecidable

noncomputable def cellSource {p : ℕ} (H : ℕ) (sources : List (InputSource p)) : Cell M.tm H → InputSource p := by
  classical
  exact fun cell => match cell with
    | .inl q => .constant (decide ((some M.tm.main,M.tm.initialState) = q))
    | .inr ⟨k,(i,a)⟩ =>
      if hk : k = M.tm.k₀ then
        let a' : Option (Symbol M.tm M.tm.k₀) := hk ▸ a
        match sources[i.val]? with
        | none => .constant (decide ((none : Option (M.tm.Γ M.tm.k₀)) = a'.map Subtype.val))
        | some s => s.map (fun b => decide (some (M.inputAlphabet.invFun b) = a'.map Subtype.val))
      else .constant (decide ((none : Option (M.tm.Γ k)) = a.map Subtype.val))

/-- Each code bit of the initial machine configuration is a constant or an
individual (possibly negated) certificate bit. -/
theorem cellSource_correct {p : ℕ} (H : ℕ) (sources : List (InputSource p)) (w : Fin p → Bool)
    (cell : Cell M.tm H) :
    (cellSource M H sources cell).evaluate w =
      encode M.tm H (Turing.initList M.tm
        ((sources.map (fun s => s.evaluate w)).map M.inputAlphabet.invFun)) cell := by
  classical
  cases cell with
  | inl q => rfl
  | inr c =>
    rcases c with ⟨k,i,a⟩
    by_cases hk : k = M.tm.k₀
    · subst k
      cases hs : sources[i.val]? with
      | none => simp [cellSource,encode,Turing.initList,InputSource.evaluate,List.getElem?_map,hs]
      | some s => simp [cellSource,encode,Turing.initList,List.getElem?_map,hs]
    · simp [cellSource,encode,Turing.initList,hk,InputSource.evaluate]

noncomputable def sources (x : BitString) (m : ℕ) : Fin (bitCount M.tm (height M x m)) → InputSource m :=
  fun i => cellSource M (height M x m) (certificateSources x m) ((cellEnumeration M.tm (height M x m)).symm i)

/-- The exact input pattern supplied to the local-network CNF constructor. -/
theorem sources_correct (x : BitString) (m : ℕ) (w : Fin m → Bool) :
    InitialNetwork.initial (sources M x m) w = encodeFin M.tm (height M x m) (initial M x w) := by
  funext i
  change (cellSource M _ _ _).evaluate w = _
  rw [cellSource_correct,certificateSources_evaluate]
  rfl

end VerifierTableau
end HiddenCircuits.Complexity
