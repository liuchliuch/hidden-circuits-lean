import HiddenCircuits.GraphReduction.Runtime.DescriptorOddParse
import HiddenCircuits.GraphReduction.Runtime.DescriptorEvenParts
import HiddenCircuits.Circuit.Runtime.SamplePairParser

namespace HiddenCircuits.GraphReduction.Runtime.DescriptorOdd
open Complexity OracleBlock BinaryArithmetic DescriptorFront WordGraph
set_option maxHeartbeats 800000

def vertex {p : ℕ} (layer : ℕ) (P : CutPair p) : VertexRecord := ⟨true,false,layer,0,cutCode P⟩
def records {p : ℕ} (width : ℕ) : ℕ → List (CutPair p) → List VertexRecord
  | _,[] => []
  | layer,P::ps => DescriptorRow.records (vertex layer P) width ++ records width (layer+1) ps

def outerEmbedding : Fin 4 ↪ Fin 20 where
  toFun i := (![16,14,6,7] : Fin 4 → Fin 20) i
  inj' := by decide +kernel
def parseEmbedding : Fin 4 ↪ Fin 20 where
  toFun i := (![14,0,3,15] : Fin 4 → Fin 20) i
  inj' := by decide +kernel
noncomputable def parse : OracleBlock 19 := seq (clear 0)
  (seq (Circuit.Runtime.SamplePairParser.on outerEmbedding) (rename DescriptorOddParse.program parseEmbedding))
noncomputable def restore : OracleBlock 19 := seq (clear 0) (seq (clear 3) (prepend 0 [false,false,false,false,false,false]))
noncomputable def body : OracleBlock 19 := seq parse (seq row (seq restore (push 1 true)))

lemma parse_executes {p : ℕ} (g : BitString → ℕ) (P : CutPair p) (layer width height samples : ℕ)
    (S T rest out : BitString) (count : ℕ) :
    parse.Executes g (workState (DescriptorEven.vertex layer) width height samples 0 [] S T (pairBits (pairAtom P) rest) out count)
      (workState (vertex layer P) width height samples 0 [] S T rest out count) (7*(cutCode P).index+79) := by
  let start := workState (DescriptorEven.vertex layer) width height samples 0 [] S T (pairBits (pairAtom P) rest) out count
  let a := Function.update start (0:Fin 20) []
  let b := Function.update (Function.update (workState (DescriptorEven.vertex layer) width height samples 0 [] S T rest out count) (0:Fin 20) []) 14 (pairAtom P)
  have h₁ : (clear (0:Fin 20)).Executes g start a 7 := clear_executes g (0:Fin 20) start
  have h₂ : (Circuit.Runtime.SamplePairParser.on outerEmbedding).Executes g a b (5*(pairAtom P).length+7) := by
    apply Circuit.Runtime.SamplePairParser.on_executes outerEmbedding g (pairAtom P) rest
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi
      have h16 : i.val≠16 := by intro h;exact hi 0 (Fin.ext h.symm)
      have h14 : i≠14 := by intro h;subst i;exact hi 1 rfl
      by_cases h0:i=0
      · subst i;rfl
      · simp only [b,a,start,Function.update_of_ne h14,Function.update_of_ne h0,workState,h16,if_false]
  have h₃ : (rename DescriptorOddParse.program parseEmbedding).Executes g b
      (workState (vertex layer P) width height samples 0 [] S T rest out count) (2*(cutCode P).index+41) := by
    apply rename_executes_to DescriptorOddParse.program parseEmbedding g (DescriptorOddParse.program_executes g (cutCode P))
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi
      have h0 : i≠0 := by intro h;subst i;exact hi 1 rfl
      have h3 : i.val≠3 := by intro h;exact hi 2 (Fin.ext h.symm)
      have h14 : i≠14 := by intro h;subst i;exact hi 0 rfl
      simp only [b,Function.update_of_ne h14,Function.update_of_ne h0]
      by_cases hlow:i.val<8
      · simp only [workState,hlow,↓reduceDIte,DescriptorAtom.state,DescriptorAtom.tagBits,vertex,DescriptorEven.vertex,backgroundCode]
        have hi0 : i.val≠0 := by intro h;exact h0 (Fin.ext h)
        simp only [hi0,h3,if_false]
      · simp only [workState,hlow,↓reduceDIte]
  convert seq_executes _ _ g h₁ (seq_executes _ _ g h₂ h₃) using 1
  rw [pairAtom_length]
  omega

lemma restore_executes {p : ℕ} (g : BitString → ℕ) (P : CutPair p) (layer width height samples : ℕ)
    (S T rest out : BitString) (count : ℕ) :
    restore.Executes g (workState (vertex layer P) width height samples 0 [] S T rest out count)
      (workState (DescriptorEven.vertex layer) width height samples 0 [] S T rest out count) ((cutCode P).index+31) := by
  let s := workState (vertex layer P) width height samples 0 [] S T rest out count
  let a := Function.update s (0:Fin 20) []
  let b := Function.update a (3:Fin 20) []
  have h₁ : (clear (0:Fin 20)).Executes g s a 7 := clear_executes g (0:Fin 20) s
  have h₂ : (clear (3:Fin 20)).Executes g a b ((cutCode P).index+1) := by
    simpa [a,s,workState,DescriptorAtom.state,vertex] using clear_executes g (3:Fin 20) a
  have h₃ : (prepend (0:Fin 20) [false,false,false,false,false,false]).Executes g b
      (workState (DescriptorEven.vertex layer) width height samples 0 [] S T rest out count) 19 := by
    convert prepend_executes g (0:Fin 20) [false,false,false,false,false,false] b using 1
    funext i;fin_cases i <;> rfl
  convert seq_executes _ _ g h₁ (seq_executes _ _ g h₂ h₃) using 1 <;> omega

theorem body_executes {p : ℕ} (g : BitString → ℕ) (P : CutPair p) (layer height samples : ℕ)
    (S T rest out : BitString) (count : ℕ) :
    ∃c,body.Executes g (workState (DescriptorEven.vertex layer) (2*p) height samples 0 [] S T (pairBits (pairAtom P) rest) out count)
      (workState (DescriptorEven.vertex (layer+1)) (2*p) height samples 0 [] S T rest
        ((encodeBitList ((DescriptorRow.records (vertex layer P) (2*p)).map encodeVertex)).reverse++out) (count+2*p)) c ∧
      c≤(2*p)*(20*layer+34*(2*p)+125)+8*(2*p)+125 := by
  have h₁ := parse_executes g P layer (2*p) height samples S T rest out count
  obtain ⟨c,h₂,hb⟩ := row_executes g (vertex layer P) rfl (2*p) height samples 0 S T rest out count
  let next := (encodeBitList ((DescriptorRow.records (vertex layer P) (2*p)).map encodeVertex)).reverse++out
  have h₃ := restore_executes g P layer (2*p) height samples S T rest next (count+2*p)
  have h₄ := DescriptorEven.increment_layer g (DescriptorEven.vertex layer) (2*p) height samples 0 S T rest next (count+2*p)
  refine ⟨_,seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ h₄)),?_⟩
  have hi := cutCode_index_le P
  dsimp only [vertex] at hb
  have hm : (2*p)*(20*layer+20*(2*p)+14*(cutCode P).index+125)≤(2*p)*(20*layer+34*(2*p)+125) := Nat.mul_le_mul_left (2*p) (by omega)
  omega
end HiddenCircuits.GraphReduction.Runtime.DescriptorOdd
