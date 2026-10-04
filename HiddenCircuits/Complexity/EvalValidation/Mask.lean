import HiddenCircuits.Approximation.Initialization.MaskEnumeration
import HiddenCircuits.Complexity.GraphVerifier.ReadOnlyLength
import HiddenCircuits.Complexity.GraphVerifier.RuntimeDecision
import HiddenCircuits.GraphReduction.Runtime.LocalCleanup

/-! All-input boundary-mask validation by actual selected-bit counting and
length comparisons. Header bytes are used only through their lengths. -/
namespace HiddenCircuits.Complexity.EvalValidation.Mask
open OracleBlock GraphVerifier.Runtime
open Approximation.Initialization
set_option maxHeartbeats 900000

def valid (mask p width : BitString) : Bool := decide (mask.count true=p.length) && decide (mask.length=width.length)
def store (mask p width out count words f h : BitString) : Store 13 :=
  ![mask,p,width,out,count,words,f,h,[],[],[],[],[],[]]
def countPorts : Fin 7 ↪ Fin 14 where
  toFun i:=![0,4,8,9,5,10,11] i
  inj' := by decide +kernel
def countCheckPorts : Fin 6 ↪ Fin 14 where
  toFun i:=![4,1,6,8,9,10] i
  inj' := by decide +kernel
def widthCheckPorts : Fin 6 ↪ Fin 14 where
  toFun i:=![0,2,7,8,9,10] i
  inj' := by decide +kernel
noncomputable def count : OracleBlock 13 := rename MaskEnumeration.program countPorts
noncomputable def checks : OracleBlock 13 := seq (readLengthOn countCheckPorts)
  (seq (readLengthOn widthCheckPorts) (decision 3 [6,7] (fun bs=>bs.all id)))
noncomputable def program : OracleBlock 13 := seq count (seq checks (clearList [0,4,5]))

lemma count_executes (g : BitString→ℕ) (mask p width : BitString) :
    ∃c,count.Executes g (store mask p width [] [] [] [] [])
      (store mask p width [] (List.replicate (mask.count true) true) (encodeBitList (MaskEnumeration.words 0 mask)) [] []) c ∧
      c≤55*(mask.length+1)^2 := by
  obtain ⟨c,hc,hb⟩:=MaskEnumeration.program_executes g mask
  refine ⟨c,?_,hb⟩
  apply rename_executes_to MaskEnumeration.program countPorts g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 1 rfl).elim | exact (hi 4 rfl).elim

lemma checks_executes (g : BitString→ℕ) (mask p width words : BitString) :
    ∃c,checks.Executes g (store mask p width [] (List.replicate (mask.count true) true) words [] [])
      (store mask p width [valid mask p width] (List.replicate (mask.count true) true) words [] []) c ∧
      c≤13*(mask.count true+p.length)+13*(mask.length+width.length)+58 := by
  let cnt:=List.replicate (mask.count true) true
  let f:=decide (mask.count true=p.length)
  let h:=decide (mask.length=width.length)
  let s0:=store mask p width [] cnt words [] []
  let s1:=store mask p width [] cnt words [f] []
  let s2:=store mask p width [] cnt words [f] [h]
  obtain ⟨a,ha,hab⟩:=readLengthOn_executes countCheckPorts g s0 cnt p (by funext i;fin_cases i <;> rfl)
  have he1:Function.update s0 (countCheckPorts 2) [decide (cnt.length=p.length)]=s1 := by
    funext i;fin_cases i <;> simp [s0,s1,cnt,f,countCheckPorts,store]
  rw [he1] at ha
  obtain ⟨b,hb,hbb⟩:=readLengthOn_executes widthCheckPorts g s1 mask width (by funext i;fin_cases i <;> rfl)
  have he2:Function.update s1 (widthCheckPorts 2) [decide (mask.length=width.length)]=s2 := by
    funext i;fin_cases i <;> rfl
  rw [he2] at hb
  have hd:(decision (3:Fin 14) [6,7] (fun bs=>bs.all id)).Executes g s2
      (store mask p width [valid mask p width] cnt words [] []) 8 := by
    have he:=decision_executes (3:Fin 14) [6,7] (by decide) (by decide) (fun bs=>bs.all id)
      (fun i=>if i=6 then f else h) g s2 (by
        intro i hi
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl <;> rfl)
    convert he using 1
    funext i;fin_cases i <;> simp [eraseStore,s2,store,valid,f,h]
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb hd),?_⟩
  simp only [cnt,List.length_replicate] at hab
  omega

theorem program_executes (g : BitString→ℕ) (mask p width : BitString) :
    ∃c,program.Executes g (store mask p width [] [] [] [] [])
      (store [] p width [valid mask p width] [] [] [] []) c ∧
      c≤1000*(mask.length+p.length+width.length+1)^2 := by
  let N:=mask.length+p.length+width.length+1
  let words:=encodeBitList (MaskEnumeration.words 0 mask)
  let cnt:=List.replicate (mask.count true) true
  obtain ⟨a,ha,hab⟩:=count_executes g mask p width
  obtain ⟨b,hb,hbb⟩:=checks_executes g mask p width words
  have hin:∀i,(store mask p width [] [] [] [] [] i).length≤N := by
    intro i;fin_cases i <;> simp [store,N] <;> omega
  have hs:∀i : Fin 14,(store mask p width [] cnt words [] [] i).length≤N+a:=ha.stack_bound hin
  have hwords:words.length≤N+a:=hs 5
  have hcnt:cnt.length≤N+a:=hs 4
  have hmask:mask.length≤N+a:=by dsimp [N];omega
  let final:=store mask p width [valid mask p width] cnt words [] []
  obtain ⟨c,hc,hcb⟩:=GraphReduction.Runtime.clearList_executes_local g ([0,4,5]:List (Fin 14)) final (N+a) (by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl
    · exact hmask
    · exact hcnt
    · exact hwords)
  have he:eraseStore ([0,4,5]:List (Fin 14)) final=store [] p width [valid mask p width] [] [] [] [] := by
    funext i;fin_cases i <;> simp [eraseStore,final,store]
  rw [he] at hc
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb hc),?_⟩
  have hn:mask.count true≤mask.length:=List.count_le_length
  have hpow:(mask.length+1)^2≤N^2:=Nat.pow_le_pow_left (by dsimp [N];omega) 2
  have hN:1≤N:=by dsimp [N];omega
  simp only [List.length_cons,List.length_nil] at hcb
  change _≤1000*N^2
  dsimp only [N] at *
  nlinarith
end HiddenCircuits.Complexity.EvalValidation.Mask
