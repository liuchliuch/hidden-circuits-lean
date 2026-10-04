import HiddenCircuits.Complexity.WordEncoding
import HiddenCircuits.Complexity.OracleMove
import HiddenCircuits.Complexity.BinaryArithmetic.SignedBits

/-! Separate fixed source registers from an arbitrary
concrete signed WordEval solver, with actual query/result transfer instructions. -/
namespace HiddenCircuits.Circuit.Runtime.SourceWordCall
open HiddenCircuits.Complexity OracleBlock BinaryArithmetic Polynomial

def WordSolverSpec {k : ℕ} (W : OracleBlock k) (g : BitString → ℕ) (p : Polynomial ℕ) : Prop :=
  ∀w : WordInstance,∃z : ℤ,∃c,
    W.Executes g (Function.update (fun _ => []) 0 (wordBits w))
      (Function.update (fun _ => []) 0 (signedBits z)) c ∧ w.value=(z:ℚ) ∧ c≤p.eval (wordBits w).length

def lowEmbedding (k : ℕ) : Fin 64 ↪ Fin (k+65) where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun q : Fin (k+65) => q.val) h)
def wordEmbedding (k : ℕ) : Fin (k+1) ↪ Fin (k+65) where
  toFun i := ⟨64+i.val,by omega⟩
  inj' := by intro i j h;apply Fin.ext;have hh:=congrArg Fin.val h;dsimp at hh;omega

def store {k : ℕ} (low : Store 63) (high : Store k) : Store (k+64) := fun i =>
  if h : i.val<64 then low ⟨i.val,h⟩ else high ⟨i.val-64,by omega⟩
def lifted {k : ℕ} (low : Store 63) : Store (k+64) := store low (fun _ => [])

@[simp] lemma store_low {k : ℕ} (low : Store 63) (high : Store k) (i : Fin 64) :
    store low high (lowEmbedding k i)=low i := by simp [store,lowEmbedding,i.isLt]
@[simp] lemma store_word {k : ℕ} (low : Store 63) (high : Store k) (i : Fin (k+1)) :
    store low high (wordEmbedding k i)=high i := by simp [store,wordEmbedding]
@[simp] lemma low_word_ne (k : ℕ) (i : Fin 64) (j : Fin (k+1)) : lowEmbedding k i≠wordEmbedding k j := by
  intro h;have hh:=congrArg Fin.val h;dsimp [lowEmbedding,wordEmbedding] at hh;omega
@[simp] lemma word_low_ne (k : ℕ) (i : Fin (k+1)) (j : Fin 64) : wordEmbedding k i≠lowEmbedding k j :=
  Ne.symm (low_word_ne k j i)

lemma store_ext {k : ℕ} {s t : Store (k+64)}
    (hl : s∘lowEmbedding k=t∘lowEmbedding k) (hh : s∘wordEmbedding k=t∘wordEmbedding k) : s=t := by
  funext i
  by_cases h : i.val<64
  · have hi : lowEmbedding k ⟨i.val,h⟩=i := Fin.ext rfl
    simpa only [Function.comp_def,hi] using congrFun hl ⟨i.val,h⟩
  · let j : Fin (k+1) := ⟨i.val-64,by omega⟩
    have hi : wordEmbedding k j=i := by apply Fin.ext;dsimp [wordEmbedding,j];omega
    simpa only [Function.comp_def,hi] using congrFun hh j

lemma update_low {k : ℕ} (low : Store 63) (high : Store k) (i : Fin 64) (xs : BitString) :
    Function.update (store low high) (lowEmbedding k i) xs=store (Function.update low i xs) high := by
  apply store_ext
  · funext j;simp only [Function.comp_def,Function.update_apply,(lowEmbedding k).injective.eq_iff,store_low]
  · funext j;simp only [Function.comp_def,Function.update_of_ne (word_low_ne k j i),store_word]
lemma update_word {k : ℕ} (low : Store 63) (high : Store k) (i : Fin (k+1)) (xs : BitString) :
    Function.update (store low high) (wordEmbedding k i) xs=store low (Function.update high i xs) := by
  apply store_ext
  · funext j;simp only [Function.comp_def,Function.update_of_ne (low_word_ne k j i),store_low]
  · funext j;simp only [Function.comp_def,Function.update_apply,(wordEmbedding k).injective.eq_iff,store_word]

lemma lift_executes {k : ℕ} (B : OracleBlock 63) (g : BitString → ℕ) (s t : Store 63) (c : ℕ)
    (h : B.Executes g s t c) :
    (rename B (lowEmbedding k)).Executes g (lifted s) (lifted t) c := by
  apply rename_executes_to B (lowEmbedding k) g h
  · funext i;exact store_low (k:=k) _ (fun _=>[]) i
  · funext i;exact store_low (k:=k) _ (fun _=>[]) i
  · intro i hi
    have hnot : ¬i.val<64 := by
      intro hsmall
      exact hi ⟨i.val,hsmall⟩ (Fin.ext rfl)
    simp [lifted,store,hnot]

noncomputable def load (k : ℕ) : OracleBlock (k+64) :=
  moveOn (lowEmbedding k 63) (wordEmbedding k 0) (lowEmbedding k 24)
    (low_word_ne _ _ _) ((lowEmbedding k).injective.ne (by decide : (63:Fin 64)≠24)) (word_low_ne _ _ _)
noncomputable def unload (k : ℕ) : OracleBlock (k+64) :=
  moveOn (wordEmbedding k 0) (lowEmbedding k 31) (lowEmbedding k 24)
    (word_low_ne _ _ _) (word_low_ne _ _ _) ((lowEmbedding k).injective.ne (by decide : (31:Fin 64)≠24))
noncomputable def program {k : ℕ} (W : OracleBlock k) : OracleBlock (k+64) :=
  seq (load k) (seq (rename W (wordEmbedding k)) (unload k))
noncomputable def time (p : Polynomial ℕ) : Polynomial ℕ := 7*p+12*X+14

lemma load_executes (k : ℕ) (g : BitString → ℕ) (low : Store 63) (h24 : low 24=[]) :
    (load k).Executes g (lifted low)
      (store (Function.update low 63 []) (Function.update (fun _ : Fin (k+1)=>[]) 0 (low 63))) (6*(low 63).length+5) := by
  have h := moveOn_executes g (lowEmbedding k 63) (wordEmbedding k 0) (lowEmbedding k 24)
    (low_word_ne _ _ _) ((lowEmbedding k).injective.ne (by decide : (63:Fin 64)≠24)) (word_low_ne _ _ _)
    (lifted low) (by simpa only [lifted,store_low] using h24)
  simpa only [lifted,store_low,store_word,List.append_nil,update_word,update_low] using h

lemma unload_executes (k : ℕ) (g : BitString → ℕ) (low : Store 63) (xs : BitString)
    (h24 : low 24=[]) (h31 : low 31=[]) :
    (unload k).Executes g (store low (Function.update (fun _ : Fin (k+1)=>[]) 0 xs))
      (lifted (Function.update low 31 xs)) (6*xs.length+5) := by
  have h := moveOn_executes g (wordEmbedding k 0) (lowEmbedding k 31) (lowEmbedding k 24)
    (word_low_ne _ _ _) (word_low_ne _ _ _) ((lowEmbedding k).injective.ne (by decide : (31:Fin 64)≠24))
    (store low (Function.update (fun _ : Fin (k+1)=>[]) 0 xs)) (by simpa only [store_low] using h24)
  simpa only [store_low,store_word,Function.update_self,h31,List.append_nil,update_low,update_word,
    Function.update_idem,Function.update_eq_self,lifted] using h

theorem program_executes {k : ℕ} (W : OracleBlock k) (g : BitString → ℕ) (p : Polynomial ℕ)
    (hW : WordSolverSpec W g p) (w : WordInstance) (low : Store 63)
    (h24 : low 24=[]) (h31 : low 31=[]) (h63 : low 63=wordBits w) :
    ∃z : ℤ,∃c, (program W).Executes g (lifted low)
      (lifted (Function.update (Function.update low 63 []) 31 (signedBits z))) c ∧
      w.value=(z:ℚ) ∧ c≤(time p).eval (wordBits w).length := by
  obtain ⟨z,c,hc,hz,hcb⟩ := hW w
  have hl := load_executes k g low h24
  rw [h63] at hl
  have hw : (rename W (wordEmbedding k)).Executes g
      (store (Function.update low 63 []) (Function.update (fun _ : Fin (k+1)=>[]) 0 (wordBits w)))
      (store (Function.update low 63 []) (Function.update (fun _ : Fin (k+1)=>[]) 0 (signedBits z))) c := by
    apply rename_executes_to W (wordEmbedding k) g hc
    · funext i;exact store_word _ _ i
    · funext i;exact store_word _ _ i
    · intro i hi
      have hsmall : i.val<64 := by
        by_contra h
        let j : Fin (k+1) := ⟨i.val-64,by omega⟩
        apply hi j
        apply Fin.ext
        dsimp [wordEmbedding,j]
        omega
      simp [store,hsmall]
  have hu := unload_executes k g (Function.update low 63 []) (signedBits z) (by simpa using h24) (by simpa using h31)
  have hsize := hc.stack_bound (show ∀i,(Function.update (fun _ : Fin (k+1)=>[]) 0 (wordBits w) i).length≤(wordBits w).length by
    intro i;simp only [Function.update_apply];split_ifs <;> simp) (0:Fin (k+1))
  change (signedBits z).length≤(wordBits w).length+c at hsize
  refine ⟨z,_,seq_executes _ _ g hl (seq_executes _ _ g hw hu),hz,?_⟩
  simp only [time,eval_add,eval_mul,eval_ofNat,eval_X]
  omega
end HiddenCircuits.Circuit.Runtime.SourceWordCall
