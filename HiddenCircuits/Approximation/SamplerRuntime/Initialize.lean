import HiddenCircuits.Approximation.SamplerRuntime.Diagonal
import HiddenCircuits.Approximation.SamplerRuntime.Identity
import HiddenCircuits.Approximation.SamplerRuntime.SwitchSemantics

/-! Real diagonal testing followed by identity-array generation, with no supplied matching. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.Initialize
open Complexity Complexity.OracleBlock

def state (L H output : BitString) (n : ℕ) (clock : BitString) (index : ℕ) (flag : BitString) : Store 17 := fun r =>
  if r.val=0 then L else if r.val=1 then H else if r.val=2 then output
  else if r.val=3 then List.replicate n true else if r.val=4 then clock
  else if r.val=5 then List.replicate index true else if r.val=6 then flag else []
def diagonalMap : Fin 15 ↪ Fin 18 where
  toFun i := ![0,1,4,5,6,7,8,9,10,11,12,13,14,15,16] i
  inj' := by decide +kernel
def identityMap : Fin 6 ↪ Fin 18 where
  toFun i := ![2,9,10,11,12,13] i
  inj' := by decide +kernel
noncomputable def program : OracleBlock 17 := seq (copyOn 3 4 17 (by decide) (by decide) (by decide))
  (seq (push 6 true) (seq (rename Diagonal.program diagonalMap) (seq (clear 5)
    (seq (copyOn 3 2 17 (by decide) (by decide) (by decide)) (rename Identity.program identityMap)))))

theorem program_executes (g : BitString → ℕ) (ls hs : List BitString) (n : ℕ) :
    ∃t,program.Executes g (state (encodeBitList ls) (encodeBitList hs) [] n [] 0 [])
      (state (encodeBitList ls) (encodeBitList hs) (Identity.evaluate (List.replicate n true)) n [] 0
        [Diagonal.check ls hs 0 n]) t ∧
      t≤2000*((encodeBitList ls).length+(encodeBitList hs).length+n+1)^3 := by
  let L := encodeBitList ls
  let H := encodeBitList hs
  let un := List.replicate n true
  let flag := Diagonal.check ls hs 0 n
  have h1 : (copyOn (3:Fin 18) 4 17 (by decide) (by decide) (by decide)).Executes g
      (state L H [] n [] 0 []) (state L H [] n un 0 []) (5*n+2) := by
    convert copyOn_executes g (3:Fin 18) 4 17 (by decide) (by decide) (by decide) (state L H [] n [] 0 []) rfl using 1
    · funext r;fin_cases r <;> simp [state,un]
    · simp [state]
  have h2 : (push (6:Fin 18) true).Executes g (state L H [] n un 0 []) (state L H [] n un 0 [true]) 1 := by
    convert push_executes g (6:Fin 18) true _ using 1
    funext r;fin_cases r <;> rfl
  obtain ⟨a,ha,hba⟩ := Diagonal.program_executes g ls hs un 0 true
  simp only [un,List.length_replicate,Nat.zero_add,Bool.true_and] at ha hba
  have h3 : (rename Diagonal.program diagonalMap).Executes g (state L H [] n un 0 [true])
      (state L H [] n [] n [flag]) a := by
    apply rename_executes_to Diagonal.program diagonalMap g ha
    · funext r;fin_cases r <;> rfl
    · funext r;fin_cases r <;> rfl
    · intro r hr;fin_cases r <;> first | rfl | exact False.elim (hr 2 rfl) | exact False.elim (hr 3 rfl) | exact False.elim (hr 4 rfl)
  have h4 : (clear (5:Fin 18)).Executes g (state L H [] n [] n [flag]) (state L H [] n [] 0 [flag]) (n+1) := by
    convert clear_executes g (5:Fin 18) _ using 1
    · funext r;fin_cases r <;> simp [state]
    · simp [state]
  have h5 : (copyOn (3:Fin 18) 2 17 (by decide) (by decide) (by decide)).Executes g
      (state L H [] n [] 0 [flag]) (state L H un n [] 0 [flag]) (5*n+2) := by
    convert copyOn_executes g (3:Fin 18) 2 17 (by decide) (by decide) (by decide)
      (state L H [] n [] 0 [flag]) rfl using 1
    · funext r;fin_cases r <;> simp [state,un]
    · simp [state]
  obtain ⟨b,hb,hbb⟩ := Identity.program_executes g un
  have h6 : (rename Identity.program identityMap).Executes g (state L H un n [] 0 [flag])
      (state L H (Identity.evaluate un) n [] 0 [flag]) b := by
    apply rename_executes_to Identity.program identityMap g hb
    · funext r;fin_cases r <;> rfl
    · funext r;fin_cases r <;> rfl
    · intro r hr;fin_cases r <;> first | rfl | exact False.elim (hr 0 rfl)
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3
    (seq_executes _ _ g h4 (seq_executes _ _ g h5 h6)))),?_⟩
  simp only [un,List.length_replicate] at hba hbb
  have hN : n+1≤L.length+H.length+n+1 := by omega
  have hpow := Nat.pow_le_pow_left hN 2
  dsimp [L,H] at hpow
  nlinarith

lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (push_queryFree _ _) (seq_queryFree _ _ (rename_queryFree _ _ Diagonal.program_queryFree)
    (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
      (rename_queryFree _ _ Identity.program_queryFree)))))

lemma diagonal_check_iff (ls hs : List BitString) (i n : ℕ) :
    Diagonal.check ls hs i n=true ↔
      ∀k<n,RowCheck.check ls hs (i+k) (List.replicate (i+k) true)=true := by
  induction n generalizing i with
  | zero => simp [Diagonal.check]
  | succ n ih =>
    simp only [Diagonal.check,Bool.and_eq_true,ih]
    constructor
    · rintro ⟨h0,hs⟩ k hk
      cases k with
      | zero => simpa using h0
      | succ k => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hs k (by omega)
    · intro h
      refine ⟨by simpa using h 0 (by omega),?_⟩
      intro k hk
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h (k+1) (by omega)

open GraphReduction.MonotoneEndpointEncoding Approximation

lemma identity_admissible {n : ℕ} (E : MonotoneEndpoints n)
    (h : Diagonal.check (rows E.lo) (rows E.hi) 0 n=true) : E.Admissible (Equiv.refl (Fin n)) := by
  intro i
  have hi := (diagonal_check_iff _ _ _ _).mp h i.val i.isLt
  simpa [RowCheck.check,IntervalCheck.check,Switch.rows_get] using hi

lemma flag_nonempty {n : ℕ} (E : MonotoneEndpoints n) :
    Diagonal.check (rows E.lo) (rows E.hi) 0 n=true ↔ Nonempty E.Permutations := by
  constructor
  · intro h;exact ⟨⟨Equiv.refl _,identity_admissible E h⟩⟩
  · rintro ⟨π⟩
    have hd := E.identity_admissible_of_admissible π.val π.property
    apply (diagonal_check_iff _ _ _ _).mpr
    intro k hk
    simpa [RowCheck.check,IntervalCheck.check,rows,hk] using hd ⟨k,hk⟩

end HiddenCircuits.Approximation.SamplerRuntime.Initialize
