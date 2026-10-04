import HiddenCircuits.DH.Runtime.PairSearchLoops
import HiddenCircuits.DH.Runtime.PairSearchOrder

/-! A fixed query-free exhaustive search for the first checked live reduction. -/
namespace HiddenCircuits.DH.Runtime.PairSearch
open Complexity Complexity.OracleBlock PairCheck

def store (n : ℕ) (payload marks : BitString) (found : Option (PruningModel.Action n)) : Store 30 :=
  state (n:=n) payload marks found 0 0 [] []
noncomputable def program : OracleBlock 30 := seq (copyOn 0 28 30 (by decide) (by decide) (by decide))
  (seq rowsLoop (clear 6))
def searchBudget (n : ℕ) : ℕ := n*(rowBudget n+2)+6*n+8

/-- Both loop clocks and both unary indices are physically cleared on return.
Only the three output words differ from the input store. -/
theorem program_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n) (alive : Vector Bool n) :
    ∃t, program.Executes g (store n G.bits (liveBits alive) none)
      (store n G.bits (liveBits alive) (find G alive)) t ∧ t≤searchBudget n := by
  have h1 : (copyOn (0 : Fin 31) 28 30 (by decide) (by decide) (by decide)).Executes g
      (store n G.bits (liveBits alive) none)
      (state (n:=n) G.bits (liveBits alive) none 0 0 (List.replicate n true) []) (5*n+2) := by
    convert copyOn_executes g (0 : Fin 31) 28 30 (by decide) (by decide) (by decide)
      (store n G.bits (liveBits alive) none) rfl using 1
    · funext i;fin_cases i <;> simp [store,state,rawState]
    · simp [store,state,rawState]
  obtain ⟨c,hc,hbc⟩ := rowsLoop_execution g G alive 0 n (by omega) none
  have h2 : rowsLoop.Executes g (state (n:=n) G.bits (liveBits alive) none 0 0 (List.replicate n true) [])
      (state (n:=n) G.bits (liveBits alive) (find G alive) n 0 [] []) c := by
    simpa only [Nat.zero_add,find] using whilePop_executes _ _ _ g hc
  have h3 : (clear (6 : Fin 31)).Executes g (state (n:=n) G.bits (liveBits alive) (find G alive) n 0 [] [])
      (store n G.bits (liveBits alive) (find G alive)) (n+1) := by
    convert clear_executes g (6 : Fin 31) (state (n:=n) G.bits (liveBits alive) (find G alive) n 0 [] []) using 1
    · funext i;fin_cases i <;> simp [store,state,rawState]
    · simp [state,rawState]
  exact ⟨(5*n+2)+(c+(n+1)+2)+2,seq_executes _ _ g h1 (seq_executes _ _ g h2 h3),by unfold searchBudget;omega⟩

lemma searchBudget_polynomial (n : ℕ) : searchBudget n≤2400*(n+1)^5 := by
  unfold searchBudget rowBudget bodyBudget candidateBudget
  nlinarith [Nat.zero_le (n^5),Nat.zero_le (n^4),Nat.zero_le (n^3),Nat.zero_le (n^2)]

theorem program_executes_polynomial (g : BitString → ℕ) {n : ℕ} (G : MatrixData n) (alive : Vector Bool n) :
    ∃t, program.Executes g (store n G.bits (liveBits alive) none)
      (store n G.bits (liveBits alive) (find G alive)) t ∧ t≤2400*(n+1)^5 := by
  obtain ⟨t,ht,hb⟩ := program_executes g G alive
  exact ⟨t,ht,hb.trans (searchBudget_polynomial n)⟩

/-- On every simple graph the returned action is literally the first action
of the checked row-major pruning scan, with pendant tests taking precedence. -/
theorem program_executes_graph (g : BitString → ℕ) {n : ℕ} (G : MatrixGraph n) (alive : Vector Bool n) :
    ∃t, program.Executes g (store n G.bits (liveBits alive) none)
      (store n G.bits (liveBits alive) (PruningModel.find G.graph alive)) t ∧ t≤2400*(n+1)^5 := by
  have h := program_executes_polynomial g (MatrixData.ofGraph G) alive
  rw [find_ofGraph] at h
  exact h

/-- Arbitrary payloads of the guarded matrix length have an unconditional
polynomial execution. Symmetry, looplessness, and distance heredity are absent. -/
theorem program_executes_payload (g : BitString → ℕ) (n : ℕ) (payload : BitString)
    (hp : payload.length=n*n) (alive : Vector Bool n) :
    ∃t, program.Executes g (store n payload (liveBits alive) none)
      (store n payload (liveBits alive) (find (MatrixData.ofPayload n payload hp) alive)) t ∧
      t≤2400*(n+1)^5 :=
  program_executes_polynomial g (MatrixData.ofPayload n payload hp) alive

lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ rowsLoop_queryFree (clear_queryFree _))

noncomputable def programOn {k : ℕ} (φ : Fin 31 ↪ Fin (k+1)) : OracleBlock k := rename program φ

/-- The public result is separate unary keep/removed outputs and one kind word.
All three are empty when no checked reduction exists. -/
theorem programOn_executes {k : ℕ} (φ : Fin 31 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    {n : ℕ} (G : MatrixData n) (alive : Vector Bool n)
    (hs : s∘φ=store n G.bits (liveBits alive) none) :
    ∃t, (programOn φ).Executes g s
      (Function.update (Function.update (Function.update s (φ 3) (keptBits (find G alive)))
        (φ 4) (removedBits (find G alive))) (φ 5) (resultBits (find G alive))) t ∧
      t≤2400*(n+1)^5 := by
  obtain ⟨t,ht,hb⟩ := program_executes_polynomial g G alive
  refine ⟨t,?_,hb⟩
  apply rename_executes_to program φ g ht hs
  · have he : (Function.update (Function.update (Function.update s (φ 3) (keptBits (find G alive)))
        (φ 4) (removedBits (find G alive))) (φ 5) (resultBits (find G alive)))∘φ =
        Function.update (Function.update (Function.update (s∘φ) 3 (keptBits (find G alive)))
          4 (removedBits (find G alive))) 5 (resultBits (find G alive)) := by
      funext i;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i;fin_cases i <;> rfl
  · intro i hi
    simp only [Function.update_of_ne (hi 5).symm,Function.update_of_ne (hi 4).symm,
      Function.update_of_ne (hi 3).symm]

lemma programOn_queryFree {k : ℕ} (φ : Fin 31 ↪ Fin (k+1)) : (programOn φ).QueryFree :=
  rename_queryFree _ _ program_queryFree

end HiddenCircuits.DH.Runtime.PairSearch
