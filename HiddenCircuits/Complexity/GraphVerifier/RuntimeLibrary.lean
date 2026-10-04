import HiddenCircuits.Complexity.GraphVerifier.UnpairProgram
import HiddenCircuits.Complexity.GraphVerifier.LookupProgram
import HiddenCircuits.Complexity.OracleCleanup

/-! Frame-preserving reusable blocks for the verifier's actual parser and indexed reads. -/
namespace HiddenCircuits.Complexity.GraphVerifier.Runtime
open OracleBlock

def unpairBlock : OracleBlock 3 where
  labelCount := 10
  start := 0
  exit := 9
  code := unpairMachine.code
  exit_halt := rfl

def parseStore (data left temporary flag : BitString) : Store 3 :=
  Fin.cases data (Fin.cases left (Fin.cases temporary (fun _ => flag)))

theorem unpairBlock_executes (g : BitString → ℕ) (xs : BitString) :
    unpairBlock.Executes g (parseStore xs [] [] [])
      (parseStore (parse xs).right (parse xs).left [] [(parse xs).ok])
      (parseCost xs+2*(parse xs).left.length+1) := by
  obtain ⟨d,hd,hc⟩ := OracleMachine.steps_embed unpairMachine unpairBlock.machine
    (Function.Embedding.refl _) id
    (by intro q h; change unpairMachine.code q = _; cases unpairMachine.code q <;> rfl) g
    (d := unpairBlock.config unpairBlock.start (parseStore xs [] [] [])) ⟨rfl,fun _ => rfl⟩
    (unpair_runs g xs).toSteps
  have he : d=unpairBlock.config unpairBlock.exit
      (parseStore (parse xs).right (parse xs).left [] [(parse xs).ok]) := OracleConfig.ext hc.1 hc.2
  rwa [he] at hd

 theorem unpairBlock_queryFree : unpairBlock.QueryFree := by
  intro q i o next
  fin_cases q <;> simp [OracleBlock.machine,unpairBlock,unpairMachine]

 def lookupBlock : OracleBlock 4 where
  labelCount := 19
  start := 0
  exit := 18
  code := Lookup.machine.code
  exit_halt := rfl

 def lookupStore (data index output tempData tempIndex : BitString) : Store 4 :=
  Fin.cases data (Fin.cases index (Fin.cases output (Fin.cases tempData (fun _ => tempIndex))))

 theorem lookupBlock_executes (g : BitString → ℕ) (data index : BitString) :
    lookupBlock.Executes g (lookupStore data index [] [] [])
      (lookupStore data index (data[index.length]?.toList) [] []) (Lookup.cost data index) := by
  obtain ⟨d,hd,hc⟩ := OracleMachine.steps_embed Lookup.machine lookupBlock.machine
    (Function.Embedding.refl _) id
    (by intro q h; change Lookup.machine.code q = _; cases Lookup.machine.code q <;> rfl) g
    (d := lookupBlock.config lookupBlock.start (lookupStore data index [] [] [])) ⟨rfl,fun _ => rfl⟩
    (Lookup.lookup_steps g data index)
  have he : d=lookupBlock.config lookupBlock.exit
      (lookupStore data index ((data.drop index.length).take 1) [] []) := OracleConfig.ext hc.1 hc.2
  rw [he] at hd
  simpa only [Lookup.take_drop_lookup] using hd

 theorem lookupBlock_queryFree : lookupBlock.QueryFree := by
  intro q i o next
  fin_cases q <;> simp [OracleBlock.machine,lookupBlock,Lookup.machine]

/-- The five indexed-read stacks can be explicitly assigned anywhere in the verifier. -/
def lookupOn {k : ℕ} (φ : Fin 5 ↪ Fin (k+1)) : OracleBlock k := rename lookupBlock φ

 theorem lookupOn_executes {k : ℕ} (φ : Fin 5 ↪ Fin (k+1)) (g : BitString → ℕ)
    (s t : Store k) (data index : BitString)
    (hs : s ∘ φ=lookupStore data index [] [] [])
    (ht : t ∘ φ=lookupStore data index (data[index.length]?.toList) [] [])
    (hf : ∀ j, (∀ i, φ i≠j) → t j=s j) :
    (lookupOn φ).Executes g s t (Lookup.cost data index) :=
  rename_executes_to lookupBlock φ g (lookupBlock_executes g data index) hs ht hf

 theorem lookupOn_queryFree {k : ℕ} (φ : Fin 5 ↪ Fin (k+1)) : (lookupOn φ).QueryFree :=
  rename_queryFree lookupBlock φ lookupBlock_queryFree

 def unpairOn {k : ℕ} (φ : Fin 4 ↪ Fin (k+1)) : OracleBlock k := rename unpairBlock φ

 theorem unpairOn_executes {k : ℕ} (φ : Fin 4 ↪ Fin (k+1)) (g : BitString → ℕ)
    (s t : Store k) (xs : BitString)
    (hs : s ∘ φ=parseStore xs [] [] [])
    (ht : t ∘ φ=parseStore (parse xs).right (parse xs).left [] [(parse xs).ok])
    (hf : ∀ j, (∀ i, φ i≠j) → t j=s j) :
    (unpairOn φ).Executes g s t (parseCost xs+2*(parse xs).left.length+1) :=
  rename_executes_to unpairBlock φ g (unpairBlock_executes g xs) hs ht hf

 theorem unpairOn_queryFree {k : ℕ} (φ : Fin 4 ↪ Fin (k+1)) : (unpairOn φ).QueryFree :=
  rename_queryFree unpairBlock φ unpairBlock_queryFree

end HiddenCircuits.Complexity.GraphVerifier.Runtime
