import HiddenCircuits.Complexity.TM2Space

/-! The finite TM2 model permits arbitrary internal stack types. This module
extracts the finite alphabet actually reachable from its finite syntax and finite
control state. No finite-internal-alphabet hypothesis is assumed. -/
namespace HiddenCircuits.Complexity.TM2Alphabet
open Turing.TM2
attribute [local instance] Classical.propDecidable
variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}
noncomputable section
local instance (priority := 2000) : DecidableEq ((k : K) × Γ k) := Classical.decEq _

/-- All tagged symbols a statement can ever push, for any control state. -/
noncomputable def symbols [Fintype σ] : Stmt Γ Λ σ → Finset ((k : K) × Γ k)
  | .push k f s => (Finset.univ.image (fun v : σ => (⟨k,f v⟩ : (k : K) × Γ k))) ∪ symbols s
  | .peek _ _ s => symbols s
  | .pop _ _ s => symbols s
  | .load _ s => symbols s
  | .branch _ s t => symbols s ∪ symbols t
  | .goto _ => ∅
  | .halt => ∅

/-- Every current stack entry lies in the specified finite alphabet. -/
def Supported (A : Finset ((k : K) × Γ k)) (S : ∀ k, List (Γ k)) : Prop :=
  ∀ k a, a ∈ S k → (⟨k,a⟩ : (k : K) × Γ k) ∈ A

variable [Fintype σ] [DecidableEq K]

theorem stepAux_supported (s : Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k))
    (A : Finset ((k : K) × Γ k)) (hS : Supported A S) (hA : symbols s ⊆ A) :
    Supported A (stepAux s v S).stk := by
  classical
  induction s generalizing v S with
  | push k f s ih =>
    apply ih
    · intro j a ha
      by_cases hj : j = k
      · subst j
        simp only [Function.update_self,List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact hA (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩))
        · exact hS k a ha
      · simp only [Function.update_of_ne hj] at ha
        exact hS j a ha
    · exact fun x hx => hA (Finset.mem_union_right _ hx)
  | peek k f s ih => exact ih _ _ hS hA
  | pop k f s ih =>
    apply ih
    · intro j a ha
      by_cases hj : j = k
      · subst j
        simp only [Function.update_self] at ha
        exact hS k a (List.mem_of_mem_tail ha)
      · simp only [Function.update_of_ne hj] at ha
        exact hS j a ha
    · exact hA
  | load f s ih => exact ih _ _ hS hA
  | branch f s t ihs iht =>
    cases hf : f v with
    | false =>
      simpa [stepAux,hf] using iht v S hS (fun x hx => hA (Finset.mem_union_right _ hx))
    | true =>
      simpa [stepAux,hf] using ihs v S hS (fun x hx => hA (Finset.mem_union_left _ hx))
  | goto f => exact hS
  | halt => exact hS

/-- Actual finite alphabet: all input symbols plus every symbol any finite control
statement can push. -/
noncomputable def alphabet (M : Turing.FinTM2) : Finset ((k : M.K) × M.Γ k) := by
  classical
  letI := M.σFin
  letI := M.ΛFin
  letI := M.Γk₀Fin
  exact (Finset.univ.image (fun a : M.Γ M.k₀ => (⟨M.k₀,a⟩ : (k : M.K) × M.Γ k))) ∪
    Finset.univ.biUnion (fun l : M.Λ => symbols (M.m l))

theorem statement_symbols_subset (M : Turing.FinTM2) (l : M.Λ) :
    letI := M.σFin
    symbols (M.m l) ⊆ alphabet M := by
  classical
  letI := M.σFin
  letI := M.ΛFin
  letI := M.Γk₀Fin
  intro x hx
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨l,Finset.mem_univ _,hx⟩)

theorem initial_supported (M : Turing.FinTM2) (x : List (M.Γ M.k₀)) :
    Supported (alphabet M) (Turing.initList M x).stk := by
  classical
  letI := M.σFin
  letI := M.ΛFin
  letI := M.Γk₀Fin
  intro k a ha
  by_cases hk : k = M.k₀
  · subst k
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)
  · simp [Turing.initList,hk] at ha

theorem step_supported (M : Turing.FinTM2) (c d : M.Cfg)
    (h : M.step c = some d) (hc : Supported (alphabet M) c.stk) :
    Supported (alphabet M) d.stk := by
  classical
  letI := M.σFin
  rcases c with ⟨label,v,S⟩
  cases label with
  | none => contradiction
  | some l =>
    have hd : d = stepAux (M.m l) v S := (Option.some.inj h).symm
    subst d
    exact stepAux_supported _ _ _ _ hc (statement_symbols_subset M l)

theorem stutter_supported (M : Turing.FinTM2) (c : M.Cfg)
    (hc : Supported (alphabet M) c.stk) : Supported (alphabet M) (stutter M.step c).stk := by
  cases h : M.step c with
  | none => rw [stutter_halt h]; exact hc
  | some d =>
    unfold stutter
    rw [h]
    exact step_supported M c d h hc

/-- Every cell of every actual input tableau uses the extracted finite alphabet. -/
theorem tableau_supported (M : Turing.FinTM2) (x : List (M.Γ M.k₀)) (t : ℕ) :
    Supported (alphabet M) (((stutter M.step)^[t] (Turing.initList M x)).stk) := by
  induction t with
  | zero => exact initial_supported M x
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact stutter_supported M _ ih

end
end HiddenCircuits.Complexity.TM2Alphabet
