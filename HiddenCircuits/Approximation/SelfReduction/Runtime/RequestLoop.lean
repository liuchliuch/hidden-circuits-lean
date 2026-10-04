import HiddenCircuits.Approximation.SelfReduction.Runtime.RequestBody
import HiddenCircuits.Approximation.SelfReduction.Runtime.MapLoop

/-! A finite generator of all real sampler requests from one contiguous fair-bit
stream. Every input/output bit and random block is accounted for. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

noncomputable def requestLoop : OracleBlock 10 := whilePop 3 requestBody requestBody
noncomputable def requestGenerator : OracleBlock 10 := seq requestLoop (reverseOn 4 6 (by decide))

 theorem encoded_requests_length (context : BitString) (blocks : List BitString) (width : ℕ)
    (hblocks : ∀ bits ∈ blocks, bits.length=width) :
    (encodeBitList (blocks.map (fun bits => pairBits context bits))).length =
      blocks.length*(4*context.length+2*width+4) := by
  induction blocks with
  | nil => simp [encodeBitList]
  | cons bits blocks ih =>
    have hb := hblocks bits (by simp)
    have ht := ih (fun x hx => hblocks x (by simp [hx]))
    simp only [List.map_cons,encodeBitList,List.length_cons,pairBits_length,hb,ht]
    ring

 theorem requestLoop_execution (g : BitString → ℕ) (context rest out : BitString)
    (blocks : List BitString) (width : ℕ) (hblocks : ∀ bits ∈ blocks, bits.length=width) :
    WhileExecution (3 : Fin 11) requestBody requestBody g
      (requestStore (blocks.flatten++rest) context out width blocks.length [] [] [])
      (requestStore rest context
        ((encodeBitList (blocks.map (fun bits => pairBits context bits))).reverse ++ out) width 0 [] [] [])
      (blocks.length*(18*width+25*context.length+38)+1) := by
  induction blocks generalizing out with
  | nil =>
    simpa [encodeBitList] using (WhileExecution.empty (requestStore rest context out width 0 [] [] []) (by rfl))
  | cons bits blocks ih =>
    have hbwidth := hblocks bits (by simp)
    have hb := requestBody_executes g bits (blocks.flatten++rest) context out width blocks.length hbwidth
    have hpop : Function.update
        (requestStore ((bits::blocks).flatten++rest) context out width (bits::blocks).length [] [] [])
        (3 : Fin 11) (List.replicate blocks.length true) =
        requestStore (bits++(blocks.flatten++rest)) context out width blocks.length [] [] [] := by
      funext i; fin_cases i <;> simp [requestStore,List.flatten_cons,List.append_assoc]
    have ht := ih ((true::pairBits (pairBits context bits) []).reverse ++ out)
      (fun x hx => hblocks x (by simp [hx]))
    have h := WhileExecution.one
      (s := requestStore ((bits::blocks).flatten++rest) context out width (bits::blocks).length [] [] [])
      (rest := List.replicate blocks.length true) (by rfl) (by rw [hpop]; exact hb) ht
    convert h using 1
    · simp only [List.map_cons,encodeBitList_cons_segment,List.reverse_append,List.append_assoc]
    · simp only [List.length_cons]
      ring

 theorem requestGenerator_executes (g : BitString → ℕ) (context rest : BitString)
    (blocks : List BitString) (width : ℕ) (hblocks : ∀ bits ∈ blocks, bits.length=width) :
    requestGenerator.Executes g
      (requestStore (blocks.flatten++rest) context [] width blocks.length [] [] [])
      (requestStore rest context [] width 0 []
        (encodeBitList (blocks.map (fun bits => pairBits context bits))) [])
      (blocks.length*(22*width+33*context.length+46)+4) := by
  have hl : requestLoop.Executes g (requestStore (blocks.flatten++rest) context [] width blocks.length [] [] [])
      (requestStore rest context (encodeBitList (blocks.map (fun bits => pairBits context bits))).reverse width 0 [] [] [])
      (blocks.length*(18*width+25*context.length+38)+1) := by
    simpa using whilePop_executes _ _ _ g (requestLoop_execution g context rest [] blocks width hblocks)
  have hr : (reverseOn (4 : Fin 11) 6 (by decide)).Executes g
      (requestStore rest context (encodeBitList (blocks.map (fun bits => pairBits context bits))).reverse width 0 [] [] [])
      (requestStore rest context [] width 0 [] (encodeBitList (blocks.map (fun bits => pairBits context bits))) [])
      (2*(encodeBitList (blocks.map (fun bits => pairBits context bits))).length+1) := by
    convert reverseOn_executes g (4 : Fin 11) 6 (by decide)
      (requestStore rest context (encodeBitList (blocks.map (fun bits => pairBits context bits))).reverse width 0 [] [] []) using 1
    · funext i; fin_cases i <;> simp [requestStore]
    · simp [requestStore]
  have h := seq_executes _ _ g hl hr
  convert h using 1
  rw [encoded_requests_length context blocks width hblocks]
  ring

end HiddenCircuits.Approximation.SelfReduction.Runtime
