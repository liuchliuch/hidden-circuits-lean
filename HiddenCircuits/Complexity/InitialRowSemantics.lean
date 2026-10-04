import HiddenCircuits.Complexity.InitialRowProgram
import HiddenCircuits.Complexity.CellEnumeration

namespace HiddenCircuits.Complexity.InitialRowFamily

theorem walkBits_ofFn {α : Type*} (chunk : α → ℕ → BitString) (n : ℕ) (f : Fin n → α) (target : ℕ) :
    walkBits chunk (List.ofFn f) target =
      (List.ofFn (fun i => chunk (f i) (target+i.val))).flatten := by
  induction n generalizing target with
  | zero => simp [walkBits]
  | succ n ih =>
    rw [List.ofFn_succ,walkBits,ih,List.ofFn_succ,List.flatten_cons]
    simp only [Fin.val_zero,Fin.val_succ,Nat.add_zero]
    apply congrArg₂ List.append rfl
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext i
    congr 1 <;> omega

lemma walkBits_congr {α : Type*} (f g : α → ℕ → BitString)
    (items : List α) (h : ∀ a ∈ items, ∀ t, f a t=g a t) (t : ℕ) :
    walkBits f items t = walkBits g items t := by
  induction items generalizing t with
  | nil => rfl
  | cons a as ih =>
    simp only [walkBits]
    rw [h a (by simp)]
    exact congrArg _ (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)) _)
end HiddenCircuits.Complexity.InitialRowFamily

namespace HiddenCircuits.Complexity.InitialRowEmitter
open TM2BooleanEncoding InitialSourceClassifier
variable {v : BitString → Bool}
variable (M : Turing.TM2ComputableInPolyTime id Computability.encodeBool v)
variable {p : ℕ}

noncomputable def slotSource (s : Symbols M.tm) : Option (InputSource p) → InputSource p
  | none => .constant (emptyValue M s)
  | some src => src.map (symbolMap M s)

noncomputable def slotBits (target : ℕ) (src : Option (InputSource p)) : BitString :=
  InitialRowFamily.walkBits (fun s i => InitialCellEmitter.bits i (slotSource M s src))
    (InitialRowFamily.symbols M.tm) target

lemma slotBits_empty (source target : ℕ) :
    InitialRowFamily.symbolBits M .empty source target = slotBits (p:=p) M target none := rfl
lemma slotBits_value (source target : ℕ) (b : Bool) :
    InitialRowFamily.symbolBits M (.value b) source target = slotBits (p:=p) M target (some (.constant b)) := rfl
lemma slotBits_witness (i : Fin p) (target : ℕ) :
    InitialRowFamily.symbolBits M .witness i.val target = slotBits M target (some (.bit i false)) := by
  apply InitialRowFamily.walkBits_congr
  intro s hs target
  exact symbolBits_witness M s i target

noncomputable def sourceListBits : ℕ → List (InputSource p) → BitString
  | _, [] => []
  | target, s::ss => slotBits M target (some s) ++ sourceListBits (target+symbolBits M.tm) ss

lemma sourceListBits_append (target : ℕ) (xs ys : List (InputSource p)) :
    sourceListBits M target (xs++ys) = sourceListBits M target xs ++
      sourceListBits M (target+xs.length*symbolBits M.tm) ys := by
  induction xs generalizing target with
  | nil => simp [sourceListBits]
  | cons x xs ih =>
    simp only [List.cons_append,sourceListBits,ih,List.length_cons,List.append_assoc]
    congr 2
    ring

noncomputable def scanBits : ℕ → ℕ → List (InputSource p) → BitString
  | _, 0, _ => []
  | target, count+1, sources => slotBits M target sources.head? ++
      scanBits (target+symbolBits M.tm) count sources.tail

lemma scanBits_ofFn (target count : ℕ) (sources : List (InputSource p)) :
    scanBits M target count sources =
      (List.ofFn (fun i : Fin count => slotBits M (target+i.val*symbolBits M.tm) sources[i.val]?)).flatten := by
  induction count generalizing target sources with
  | zero => simp [scanBits]
  | succ count ih =>
    rw [scanBits,ih,List.ofFn_succ,List.flatten_cons]
    simp only [Fin.val_zero,Fin.val_succ,Nat.zero_mul,Nat.add_zero]
    apply congrArg₂ List.append (by cases sources <;> rfl)
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext i
    simp only [List.getElem?_tail]
    congr 1 <;> ring

lemma scanBits_list (target count : ℕ) (sources : List (InputSource p)) :
    scanBits M target (sources.length+count) sources =
      sourceListBits M target sources ++ scanBits (p:=p) M (target+sources.length*symbolBits M.tm) count [] := by
  induction sources generalizing target with
  | nil => simp [scanBits,sourceListBits]
  | cons s ss ih =>
    rw [List.length_cons,show ss.length+1+count=(ss.length+count)+1 by omega,scanBits]
    simp only [List.head?_cons,List.tail_cons,sourceListBits]
    rw [ih,List.append_assoc]
    congr 2
    ring

lemma paddingBits_eq_scan (source target count : ℕ) :
    paddingBits M source target count = scanBits (p:=p) M target count [] := by
  induction count generalizing target with
  | zero => rfl
  | succ count ih => simp [paddingBits,scanBits,slotBits_empty (p:=p),ih]

lemma prefixBits_eq_sources (source target : ℕ) (x : BitString) :
    prefixBits M source target x ++
      InitialRowFamily.symbolBits M (.value false) source (target+2*x.length*symbolBits M.tm) =
      sourceListBits (p:=p) M target ((pairBits x []).map InputSource.constant) := by
  induction x generalizing target with
  | nil => simp [prefixBits,pairBits,sourceListBits,slotBits_value (p:=p)]
  | cons b bs ih =>
    simp only [prefixBits,pairBits,List.map_cons,sourceListBits,List.length_cons,List.append_assoc]
    rw [slotBits_value (p:=p),slotBits_value (p:=p)]
    congr 2
    have ht : target+symbolBits M.tm+symbolBits M.tm = target+2*symbolBits M.tm := by ring
    rw [ht]
    have hi := ih (target+2*symbolBits M.tm)
    convert hi using 1 <;> congr 2 <;> ring

lemma witnessBits_eq_sources (source target count : ℕ) (h : source+count≤p) :
    witnessBits M source target count = sourceListBits M target
      (List.ofFn (fun i : Fin count => InputSource.bit (⟨source+i.val,by have := i.isLt;omega⟩ : Fin p) false)) := by
  induction count generalizing source target with
  | zero => simp [witnessBits,sourceListBits]
  | succ count ih =>
    rw [witnessBits,List.ofFn_succ,sourceListBits]
    have hs : source<p := by omega
    rw [slotBits_witness M ⟨source,hs⟩]
    simp only [Fin.val_zero,Nat.add_zero]
    apply congrArg₂ List.append rfl
    rw [ih (source+1) (target+symbolBits M.tm) (by omega)]
    apply congrArg (sourceListBits M (target+symbolBits M.tm))
    apply congrArg List.ofFn
    funext i
    congr 2
    simp only [Fin.val_succ]
    omega

/-- The emitted stack-position stream is the direct scan of the original
certificate source list, followed by its genuine empty padding. -/
theorem bits_eq_scan (x : BitString) (m H : ℕ) (hH : 2*x.length+m+1≤H) :
    bits M x m H = InitialRowFamily.controlBits M m ++
      scanBits M (m+controlBits M.tm) H (certificateSources x m) := by
  let t := m+controlBits M.tm
  let pad := H-(2*x.length+m+1)
  have hl : (certificateSources x m).length+pad=H := by simp only [certificateSources_length]; dsimp [pad];omega
  conv_rhs => rw [←hl,scanBits_list]
  rw [certificateSources,sourceListBits_append]
  rw [←prefixBits_eq_sources M 0 t x]
  have hp : (((pairBits x []).map (InputSource.constant (inputs:=m))).length) = 2*x.length+1 := by simp
  rw [hp]
  have hw := witnessBits_eq_sources (p:=m) M 0 (t+(2*x.length+1)*symbolBits M.tm) m (by omega)
  simp only [Nat.zero_add] at hw
  rw [←hw,←paddingBits_eq_scan M m]
  dsimp [bits,t,pad]
  simp only [List.append_assoc,List.length_append,List.length_map,pairBits_length,List.length_nil,List.length_ofFn]
  congr 2 <;> ring_nf

end HiddenCircuits.Complexity.InitialRowEmitter
