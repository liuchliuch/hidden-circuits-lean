import HiddenCircuits.Approximation.SamplerRuntime.PartnerMove

namespace HiddenCircuits.Approximation.SamplerRuntime.PartnerMove
open Complexity Complexity.OracleBlock

variable {n : ℕ}

def witness (G : MatrixGraph n) (P : PerfectPartner G.graph) : BitString := Output.witness (partnerPermutation G P)

theorem program_partner (g : BitString → ℕ) (G : MatrixGraph n) (P : PerfectPartner G.graph) (a b : Fin n) :
    ∃t,program.Executes g (state n G.bits (witness G P) a.val b.val [] [] [])
      (state n G.bits (witness G (QuasimonotoneProof.PartnerSwitch.switch G.graph a b P)) a.val b.val [] [] []) t ∧
      t≤3000000*(n+1)^4 := by
  obtain ⟨t,ht,hb⟩ := program_executes g G (partnerPermutation G P) a b
  rw [result_partner] at ht
  exact ⟨t,ht,hb⟩

noncomputable def on {k : ℕ} (φ : Fin 20 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 20 ↪ Fin (k+1)) (g : BitString → ℕ) (s t : Store k)
    (G : MatrixGraph n) (P : PerfectPartner G.graph) (a b : Fin n)
    (hs : s∘φ=state n G.bits (witness G P) a.val b.val [] [] [])
    (ht : t∘φ=state n G.bits (witness G (QuasimonotoneProof.PartnerSwitch.switch G.graph a b P)) a.val b.val [] [] [])
    (hf : ∀r,(∀j,φ j≠r) → t r=s r) :
    ∃cost,(on φ).Executes g s t cost ∧ cost≤3000000*(n+1)^4 := by
  obtain ⟨c,hc,hb⟩ := program_partner g G P a b
  exact ⟨c,rename_executes_to program φ g hc hs ht hf,hb⟩

lemma on_queryFree {k : ℕ} (φ : Fin 20 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ program_queryFree

end HiddenCircuits.Approximation.SamplerRuntime.PartnerMove
