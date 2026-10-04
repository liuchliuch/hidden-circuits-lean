import HiddenCircuits.Circuit.Runtime.BoundaryMaskProgram
import HiddenCircuits.Circuit.Runtime.SamplePairParser

/-! Parse both logical boundary masks, physically surround the circuit by their
X-gate streams, and serialize the ordinary zero-boundary circuit input. -/
namespace HiddenCircuits.Circuit.Runtime.BoundaryPreprocess
open Complexity OracleBlock BinaryArithmetic Polynomial
set_option maxHeartbeats 800000

def store (input left right width out : BitString) : Store 7 := ![input,left,right,width,[],out,[],[]]
def leftParse : Fin 4 ↪ Fin 8 := ⟨fun i=>![0,1,6,7] i,by decide +kernel⟩
def rightParse : Fin 4 ↪ Fin 8 := ⟨fun i=>![0,2,6,7] i,by decide +kernel⟩
def widthParse : Fin 4 ↪ Fin 8 := ⟨fun i=>![0,3,6,7] i,by decide +kernel⟩
def leftMap : Fin 5 ↪ Fin 8 := ⟨fun i=>![1,4,5,6,7] i,by decide +kernel⟩
def rightMap : Fin 5 ↪ Fin 8 := ⟨fun i=>![2,4,5,6,7] i,by decide +kernel⟩
def pairMap : Fin 3 ↪ Fin 8 := ⟨fun i=>![0,3,6] i,by decide +kernel⟩
noncomputable def parse : OracleBlock 7 := seq (SamplePairParser.on leftParse)
  (seq (SamplePairParser.on rightParse) (SamplePairParser.on widthParse))
noncomputable def emit : OracleBlock 7 := seq (BoundaryTransport.on leftMap)
  (seq (reverseOn 0 5 (by decide)) (BoundaryTransport.on rightMap))
noncomputable def finish : OracleBlock 7 := seq (reverseOn 5 0 (by decide)) (PairSerialization.on pairMap)
noncomputable def program : OracleBlock 7 := seq parse (seq emit finish)
noncomputable def time : Polynomial ℕ := 500*(X+1)^2

def input (left right width gates : BitString) : BitString := pairBits left (pairBits right (pairBits width gates))
def result (left right width gates : BitString) : BitString := pairBits width
  (BoundaryTransport.chunks left 0++gates++BoundaryTransport.chunks right 0)
lemma parse_executes (g : BitString→ℕ) (left right width gates : BitString) :
    parse.Executes g (store (input left right width gates) [] [] [] [])
      (store gates left right width []) (5*(left.length+right.length+width.length)+25) := by
  have hl : (SamplePairParser.on leftParse).Executes g (store (input left right width gates) [] [] [] [])
      (store (pairBits right (pairBits width gates)) left [] [] []) (5*left.length+7) := by
    apply SamplePairParser.on_executes leftParse g left _
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | (exfalso;exact hi 0 rfl) | (exfalso;exact hi 1 rfl)
  have hr : (SamplePairParser.on rightParse).Executes g
      (store (pairBits right (pairBits width gates)) left [] [] [])
      (store (pairBits width gates) left right [] []) (5*right.length+7) := by
    apply SamplePairParser.on_executes rightParse g right _
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | (exfalso;exact hi 0 rfl) | (exfalso;exact hi 1 rfl)
  have hw : (SamplePairParser.on widthParse).Executes g (store (pairBits width gates) left right [] [])
      (store gates left right width []) (5*width.length+7) := by
    apply SamplePairParser.on_executes widthParse g width _
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | (exfalso;exact hi 0 rfl) | (exfalso;exact hi 1 rfl)
  convert seq_executes _ _ g hl (seq_executes _ _ g hr hw) using 1 <;> omega

lemma emit_executes (g : BitString→ℕ) (left right width gates : BitString) :
    ∃c,emit.Executes g (store gates left right width [])
      (store [] [] [] width ((BoundaryTransport.chunks left 0++gates++BoundaryTransport.chunks right 0).reverse)) c ∧
      c ≤ left.length*(14*left.length+74)+right.length*(14*right.length+74)+2*gates.length+13 := by
  obtain ⟨a,ha,hab⟩:=BoundaryTransport.on_executes leftMap g left []
    (store gates left right width []) (store gates [] right width (BoundaryTransport.chunks left 0).reverse)
    (by funext i;fin_cases i <;> rfl) (by funext i;fin_cases i <;> simp only [List.append_nil] <;> rfl)
    (by intro i hi;fin_cases i <;> first | rfl | (exfalso;exact hi 0 rfl) | (exfalso;exact hi 2 rfl))
  have hr : (reverseOn (0:Fin 8) 5 (by decide)).Executes g
      (store gates [] right width (BoundaryTransport.chunks left 0).reverse)
      (store [] [] right width (gates.reverse++(BoundaryTransport.chunks left 0).reverse)) (2*gates.length+1) := by
    convert reverseOn_executes g (0:Fin 8) 5 (by decide)
      (store gates [] right width (BoundaryTransport.chunks left 0).reverse) using 1
    · funext i;fin_cases i <;> simp [store]
  obtain ⟨b,hb,hbb⟩:=BoundaryTransport.on_executes rightMap g right
    (gates.reverse++(BoundaryTransport.chunks left 0).reverse)
    (store [] [] right width (gates.reverse++(BoundaryTransport.chunks left 0).reverse))
    (store [] [] [] width ((BoundaryTransport.chunks right 0).reverse++(gates.reverse++(BoundaryTransport.chunks left 0).reverse)))
    (by funext i;fin_cases i <;> rfl) (by funext i;fin_cases i <;> rfl)
    (by intro i hi;fin_cases i <;> first | rfl | (exfalso;exact hi 0 rfl) | (exfalso;exact hi 2 rfl))
  refine ⟨a+(2*gates.length+1+b+2)+2,?_,by omega⟩
  simpa only [List.reverse_append,List.append_assoc] using seq_executes _ _ g ha (seq_executes _ _ g hr hb)
end HiddenCircuits.Circuit.Runtime.BoundaryPreprocess
