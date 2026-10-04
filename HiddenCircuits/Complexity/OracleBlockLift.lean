import HiddenCircuits.Complexity.OracleStructured
import HiddenCircuits.Complexity.TM2BitSimulation

/-! Stack-renaming and frame-preserving block reuse. Renaming is an actual
instruction transformation; its execution theorem preserves the exact charge. -/
namespace HiddenCircuits.Complexity.OracleBlock
variable {k l : ℕ}

/-- Rename the stacks touched by a finite block, leaving the label graph intact. -/
def rename (B : OracleBlock k) (φ : Fin (k+1) ↪ Fin (l+1)) : OracleBlock l where
  labelCount := B.labelCount
  start := B.start
  exit := B.exit
  code q := OracleInstr.map φ id (B.code q)
  exit_halt := by rw [B.exit_halt];rfl

/-- Full semantic store update on the renamed stack positions. Its off-image
part is unchanged. This function is used only to state the frame invariant. -/
noncomputable def install (φ : Fin (k+1) ↪ Fin (l+1)) (outer : Store l) (inner : Store k) : Store l :=
  fun j => if h : ∃ i, φ i = j then inner (Classical.choose h) else outer j

@[simp] theorem install_image (φ : Fin (k+1) ↪ Fin (l+1)) (outer : Store l) (inner : Store k) (i : Fin (k+1)) :
    install φ outer inner (φ i) = inner i := by
  classical
  unfold install
  rw [dif_pos ⟨i,rfl⟩]
  congr 1
  exact φ.injective (Classical.choose_spec (show ∃ j, φ j = φ i from ⟨i,rfl⟩))

@[simp] theorem install_off (φ : Fin (k+1) ↪ Fin (l+1)) (outer : Store l) (inner : Store k)
    (j : Fin (l+1)) (hj : ∀ i, φ i ≠ j) : install φ outer inner j = outer j := by
  classical
  unfold install
  rw [dif_neg (by simpa using hj)]

lemma rename_embeds (B : OracleBlock k) (φ : Fin (k+1) ↪ Fin (l+1)) :
    OracleMachine.EmbedsCode B.machine (rename B φ).machine φ id := fun _ _ => rfl

/-- Every auxiliary stack outside the chosen image is preserved, and the charge
is exactly that of the original component's real instruction execution. -/
theorem rename_executes (B : OracleBlock k) (φ : Fin (k+1) ↪ Fin (l+1))
    (g : BitString → ℕ) (outer : Store l) {inner : Store k} {cost : ℕ}
    (h : B.Executes g (outer ∘ φ) inner cost) :
    (rename B φ).Executes g outer (install φ outer inner) cost := by
  obtain ⟨d,hd,hc,hframe⟩ := OracleMachine.steps_embed_frame B.machine (rename B φ).machine φ id
    (rename_embeds B φ) g (d := (rename B φ).config B.start outer) ⟨rfl,fun _ => rfl⟩ h
  have he : d = (rename B φ).config B.exit (install φ outer inner) := by
    apply OracleConfig.ext hc.1
    intro j
    by_cases hj : ∃ i, φ i = j
    · obtain ⟨i,rfl⟩ := hj
      simpa [config] using hc.2 i
    · have hne : ∀ i, φ i ≠ j := by simpa using hj
      simpa [config,install_off, hne] using hframe j hne
  rwa [he] at hd

/-- Convenient full-store form: identify both restricted stores and supply the
unchanged off-image frame, without unfolding the semantic `install` function. -/
theorem rename_executes_to (B : OracleBlock k) (φ : Fin (k+1) ↪ Fin (l+1))
    (g : BitString → ℕ) {outerS outerT : Store l} {innerS innerT : Store k} {cost : ℕ}
    (h : B.Executes g innerS innerT cost) (hS : outerS ∘ φ = innerS) (hT : outerT ∘ φ = innerT)
    (hframe : ∀ j, (∀ i, φ i ≠ j) → outerT j = outerS j) :
    (rename B φ).Executes g outerS outerT cost := by
  have hr := rename_executes B φ g outerS (by rw [hS];exact h)
  have he : install φ outerS innerT = outerT := by
    funext j
    by_cases hj : ∃ i, φ i = j
    · obtain ⟨i,rfl⟩ := hj
      rw [install_image]
      exact (congrFun hT i).symm
    · have hn : ∀ i, φ i ≠ j := by simpa using hj
      rw [install_off φ outerS innerT j hn]
      exact (hframe j hn).symm
  rwa [he] at hr

/-- A syntactic no-oracle property, usable by the actual TM2 simulator. -/
abbrev QueryFree (B : OracleBlock k) := B.machine.QueryFree

lemma instr_map_noquery {a q q' : ℕ} (instr : OracleInstr a q)
    (φ : Fin a → Fin (l+1)) (ψ : Fin q → Fin q')
    (h : ∀ i o next, instr ≠ .query i o next) :
    ∀ i o next, OracleInstr.map φ ψ instr ≠ .query i o next := by
  cases instr <;> simp [OracleInstr.map] at *

lemma rename_queryFree (B : OracleBlock k) (φ : Fin (k+1) ↪ Fin (l+1))
    (h : B.QueryFree) : (rename B φ).QueryFree := by
  intro q
  exact instr_map_noquery (B.code q) φ id (h q)

end HiddenCircuits.Complexity.OracleBlock
