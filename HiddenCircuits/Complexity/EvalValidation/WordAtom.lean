import HiddenCircuits.Complexity.EvalValidation.WordAtomSemantics
import HiddenCircuits.Complexity.EvalValidation.Prefix

/-! The canonical letter serialization is literally true,kind-bit,true,
kind-bit,false,index. The finite grammar checks those five positions, then
runs the concrete unary-index scanner. -/
namespace HiddenCircuits.Complexity.EvalValidation.WordAtom
open OracleBlock GraphVerifier
set_option maxHeartbeats 800000

def pattern : List (Option Bool) := [some true,none,some true,none,some false]
noncomputable def program : OracleBlock 8 := Prefix.read pattern
lemma prefix_shape (xs width : BitString) : Prefix.evaluate pattern xs width=
    match xs with
    | true::a::true::b::false::is => Index.valid is width
    | _ => false := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil => cases a <;> rfl
    | cons b xs =>
      cases xs with
      | nil => cases a <;> cases b <;> rfl
      | cons c xs =>
        cases xs with
        | nil => cases a <;> cases b <;> cases c <;> rfl
        | cons d xs =>
          cases xs with
          | nil => cases a <;> cases b <;> cases c <;> cases d <;> rfl
          | cons e xs => cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> rfl
lemma prefix_witness (xs width : BitString) : Prefix.evaluate pattern xs width=true ↔
    ∃a b is,xs=pairBits [a,b] is ∧ Index.valid is width=true := by
  rw [prefix_shape]
  cases xs with
  | nil => simp [pairBits]
  | cons a xs =>
    cases xs with
    | nil => cases a <;> simp [pairBits]
    | cons b xs =>
      cases xs with
      | nil => cases a <;> cases b <;> simp [pairBits]
      | cons c xs =>
        cases xs with
        | nil => cases a <;> cases b <;> cases c <;> simp [pairBits]
        | cons d xs =>
          cases xs with
          | nil => cases a <;> cases b <;> cases c <;> cases d <;> simp [pairBits]
          | cons e xs => cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> simp [pairBits]
lemma valid_witness (xs width : BitString) : valid xs width=true ↔
    ∃a b is,xs=pairBits [a,b] is ∧ Index.valid is width=true := by
  constructor
  · intro h
    have hv:(parse xs).ok=true ∧ Index.valid (parse xs).right width=true ∧ (parse xs).left.length=2 := by
      simpa only [valid,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using h
    obtain ⟨a,b,hkind⟩:=List.length_eq_two.mp hv.2.2
    refine ⟨a,b,(parse xs).right,?_,hv.2.1⟩
    have hu:unpairBits xs=some ((parse xs).left,(parse xs).right):=by rw [parse_spec,hv.1];rfl
    have he:=pairBits_of_unpair xs _ _ hu
    rw [hkind] at he
    exact he.symm
  · rintro ⟨a,b,is,rfl,h⟩
    simp [valid,parse_pair,h]
lemma prefix_eq_valid (xs width : BitString) : Prefix.evaluate pattern xs width=valid xs width :=
  Bool.eq_iff_iff.mpr ((prefix_witness xs width).trans (valid_witness xs width).symm)

theorem program_executes (g : BitString→ℕ) (xs width : BitString) :
    ∃c,program.Executes g (Index.store xs width [] [] [] [] []) (Index.store [] width [valid xs width] [] [] [] []) c ∧
      c≤500*(xs.length+width.length+1) := by
  obtain ⟨c,hc,hb⟩:=Prefix.read_executes g pattern xs width
  rw [prefix_eq_valid] at hc
  refine ⟨c,hc,?_⟩
  simp only [pattern,List.length_cons,List.length_nil] at hb
  omega
end HiddenCircuits.Complexity.EvalValidation.WordAtom
