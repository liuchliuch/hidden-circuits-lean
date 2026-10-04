import HiddenCircuits.Approximation.SamplerRuntime.UnaryDecode
import HiddenCircuits.Approximation.SamplerRuntime.TapeRead

/-! One fixed-width proposal consumes exactly the available prefix, pads absent
bits by zero, and converts the finite binary number using real unary updates. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.Proposal
open Complexity Complexity.OracleBlock

def index (m : ℕ) (source : BitString) : ℕ := UnaryDecode.little (TapeRead.takePadded m source)
def state (source width result clock reversed temporary : BitString) : Store 5 := fun r =>
  if r.val=0 then source else if r.val=1 then width else if r.val=2 then result
  else if r.val=3 then clock else if r.val=4 then reversed else temporary

def tapeMap : Fin 3 ↪ Fin 6 where
  toFun i := ![0,3,4] i
  inj' := by decide +kernel
def decodeMap : Fin 4 ↪ Fin 6 where
  toFun i := ![4,2,3,5] i
  inj' := by decide +kernel
noncomputable def program : OracleBlock 5 := seq (copyOn 1 3 5 (by decide) (by decide) (by decide))
  (seq (TapeRead.on tapeMap) (rename UnaryDecode.program decodeMap))

theorem program_executes (g : BitString → ℕ) (source width : BitString) :
    ∃t,program.Executes g (state source width [] [] [] [])
      (state (source.drop width.length) width (List.replicate (index width.length source) true) [] [] []) t ∧
      t≤10*width.length+20*(width.length+1)*2^width.length+7 := by
  let bits := (TapeRead.takePadded width.length source).reverse
  have h1 : (copyOn (1:Fin 6) 3 5 (by decide) (by decide) (by decide)).Executes g
      (state source width [] [] [] []) (state source width [] width [] []) (5*width.length+2) := by
    convert copyOn_executes g (1:Fin 6) 3 5 (by decide) (by decide) (by decide) (state source width [] [] [] []) rfl using 1
    funext r;fin_cases r <;> simp [state]
  have h2 : (TapeRead.on tapeMap).Executes g (state source width [] width [] [])
      (state (source.drop width.length) width [] [] bits []) (5*width.length+1) := by
    apply TapeRead.on_executes tapeMap g _ _ source width []
    · funext r;fin_cases r <;> rfl
    · funext r;fin_cases r <;> simp [state,tapeMap,TapeRead.state,bits]
    · intro r hr;fin_cases r <;> first | rfl | exact False.elim (hr 0 rfl) | exact False.elim (hr 1 rfl) | exact False.elim (hr 2 rfl)
  obtain ⟨c,hc,hb⟩ := UnaryDecode.program_executes g bits 0
  have h3 : (rename UnaryDecode.program decodeMap).Executes g
      (state (source.drop width.length) width [] [] bits [])
      (state (source.drop width.length) width (List.replicate (index width.length source) true) [] [] []) c := by
    apply rename_executes_to UnaryDecode.program decodeMap g hc
    · funext r;fin_cases r <;> rfl
    · funext r;fin_cases r <;> rfl
    · intro r hr;fin_cases r <;> first | rfl | exact False.elim (hr 0 rfl) | exact False.elim (hr 1 rfl)
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 h3),?_⟩
  simp only [bits,List.length_reverse,TapeRead.prefix_length,Nat.zero_add,Nat.mul_one] at hb
  omega

lemma index_lt (m : ℕ) (source : BitString) : index m source<2^m := by
  simpa [index,UnaryDecode.little,TapeRead.prefix_length] using
    UnaryDecode.value_bound 0 (TapeRead.takePadded m source).reverse

lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (TapeRead.on_queryFree _) (rename_queryFree _ _ UnaryDecode.program_queryFree))
noncomputable def on {k : ℕ} (φ : Fin 6 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 6 ↪ Fin (k+1)) (g : BitString → ℕ) (s t : Store k)
    (source width : BitString) (hs : s∘φ=state source width [] [] [] [])
    (ht : t∘φ=state (source.drop width.length) width (List.replicate (index width.length source) true) [] [] [])
    (hf : ∀r,(∀q,φ q≠r) → t r=s r) :
    ∃c,(on φ).Executes g s t c ∧ c≤10*width.length+20*(width.length+1)*2^width.length+7 := by
  obtain ⟨c,hc,hb⟩ := program_executes g source width
  exact ⟨c,rename_executes_to program φ g hc hs ht hf,hb⟩
lemma on_queryFree {k : ℕ} (φ : Fin 6 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ program_queryFree

end HiddenCircuits.Approximation.SamplerRuntime.Proposal
