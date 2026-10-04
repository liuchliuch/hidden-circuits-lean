import HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionSerializeCore
import HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionState

/-! Native coordinate-output serializer in the stable 23-stack extraction bank.
It preserves every existing input and frame field, writes output stack 13, and
cleans its scratch bank. No supplied binary coordinate bytes are used. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionSerialize
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic
open UnitCoordinateExtraction UnitCoordinateExtractionMachine

def embedding : Fin 9 ↪ Fin 23 where
  toFun i := if i.val=0 then 3 else if i.val=1 then 4 else if i.val=2 then 13
    else ⟨i.val+11,by omega⟩
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
noncomputable def program : OracleBlock 22 := rename coreProgram embedding

def bits {n : ℕ} (D : ℕ) (x : Coordinates n) : BitString :=
  encodeBitList (signedBits (D:ℤ)::List.ofFn (fun i=>signedBits (x i:ℤ)))

lemma bits_eq_native {n : ℕ} (D : ℕ) (x : Coordinates n) :
    bits D x=nativeBytes D (List.ofFn x) := by
  simp [bits,nativeBytes,binaryWords,List.map_ofFn,Function.comp_def]
lemma encoded_eq_unary {n : ℕ} (x : Coordinates n) :
    UnitCoordinateExtractionMachine.encoded x=encodeBitList (unaryWords (List.ofFn x)) := by
  simp [UnitCoordinateExtractionMachine.encoded,UnitCoordinateExtractionMachine.words,unaryWords,List.map_ofFn,Function.comp_def]

 theorem program_executes (g : BitString → ℕ) {n : ℕ} (f : Frame) (x : Coordinates n)
    (B : ℕ) (hx : ∀i,x i≤B) (hout : f.out=[]) :
    ∃t,program.Executes g (state f (UnitCoordinateExtractionMachine.encoded x) 0 0 [] [] [])
      (state {f with out:=bits f.D x} (UnitCoordinateExtractionMachine.encoded x) 0 0 [] [] []) t ∧t≤bound n f.D B := by
  obtain ⟨t,ht,hb⟩:=coreProgram_executes g f.D (List.ofFn x) B (by
    intro a ha;obtain ⟨i,rfl⟩:=List.mem_ofFn.mp ha;exact hx i)
  rw [←encoded_eq_unary,←bits_eq_native] at ht
  refine ⟨t,?_,by simpa using hb⟩
  apply rename_executes_to coreProgram embedding g ht
  · funext i;fin_cases i <;> simp [Function.comp_def,embedding,state,coreState,hout]
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 2 rfl).elim

lemma bits_length {n : ℕ} (D : ℕ) (x : Coordinates n) (B : ℕ) (hx : ∀i,x i≤B) :
    (bits D x).length≤2*D+4+n*(2*B+4) := by
  rw [bits_eq_native]
  have h:=native_length D (List.ofFn x) B (by
    intro a ha;obtain ⟨i,rfl⟩:=List.mem_ofFn.mp ha;exact hx i)
  simpa using h
lemma program_queryFree : program.QueryFree := rename_queryFree _ _ coreProgram_queryFree
end HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionSerialize
