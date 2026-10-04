import HiddenCircuits.Complexity.ConstraintEncoding
import HiddenCircuits.Complexity.OracleMove
import HiddenCircuits.Complexity.BinaryArithmetic.SignedBits

/-! Concrete native constraint-solver calls in a physically disjoint register
bank. Both transfers are finite bit programs; source metadata survives the call. -/
namespace HiddenCircuits.Circuit.Runtime.NativeConstraintCall
open HiddenCircuits.Complexity OracleBlock BinaryArithmetic Polynomial

def SolverSpec {k : ℕ} (S : OracleBlock k) (g : BitString → ℕ) (p : Polynomial ℕ) : Prop :=
  ∀C : ConstraintInput, ∃c,
    S.Executes g (Function.update (fun _ => []) 0 C.encode)
      (Function.update (fun _ => []) 0 (RationalOracleEncoding.bits C.value)) c ∧
      c≤p.eval C.encode.length

def lowEmbedding (k : ℕ) : Fin 36 ↪ Fin (k+37) where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun q : Fin (k+37) => q.val) h)
def solverEmbedding (k : ℕ) : Fin (k+1) ↪ Fin (k+37) where
  toFun i := ⟨36+i.val,by omega⟩
  inj' := by intro i j h;apply Fin.ext;have hh:=congrArg Fin.val h;dsimp at hh;omega

def store {k : ℕ} (low : Store 35) (high : Store k) : Store (k+36) := fun i =>
  if h : i.val<36 then low ⟨i.val,h⟩ else high ⟨i.val-36,by omega⟩
def lifted {k : ℕ} (low : Store 35) : Store (k+36) := store low (fun _ => [])

@[simp] lemma store_low {k : ℕ} (low : Store 35) (high : Store k) (i : Fin 36) :
    store low high (lowEmbedding k i)=low i := by simp [store,lowEmbedding,i.isLt]
@[simp] lemma store_solver {k : ℕ} (low : Store 35) (high : Store k) (i : Fin (k+1)) :
    store low high (solverEmbedding k i)=high i := by simp [store,solverEmbedding]
@[simp] lemma low_solver_ne (k : ℕ) (i : Fin 36) (j : Fin (k+1)) : lowEmbedding k i≠solverEmbedding k j := by
  intro h;have hh:=congrArg Fin.val h;dsimp [lowEmbedding,solverEmbedding] at hh;omega
@[simp] lemma solver_low_ne (k : ℕ) (i : Fin (k+1)) (j : Fin 36) : solverEmbedding k i≠lowEmbedding k j :=
  Ne.symm (low_solver_ne k j i)

lemma store_ext {k : ℕ} {s t : Store (k+36)}
    (hl : s∘lowEmbedding k=t∘lowEmbedding k) (hh : s∘solverEmbedding k=t∘solverEmbedding k) : s=t := by
  funext i
  by_cases h : i.val<36
  · have hi : lowEmbedding k ⟨i.val,h⟩=i := Fin.ext rfl
    simpa only [Function.comp_def,hi] using congrFun hl ⟨i.val,h⟩
  · let j : Fin (k+1) := ⟨i.val-36,by omega⟩
    have hi : solverEmbedding k j=i := by apply Fin.ext;dsimp [solverEmbedding,j];omega
    simpa only [Function.comp_def,hi] using congrFun hh j

lemma update_low {k : ℕ} (low : Store 35) (high : Store k) (i : Fin 36) (xs : BitString) :
    Function.update (store low high) (lowEmbedding k i) xs=store (Function.update low i xs) high := by
  apply store_ext
  · funext j;simp only [Function.comp_def,Function.update_apply,(lowEmbedding k).injective.eq_iff,store_low]
  · funext j;simp only [Function.comp_def,Function.update_of_ne (solver_low_ne k j i),store_solver]
lemma update_solver {k : ℕ} (low : Store 35) (high : Store k) (i : Fin (k+1)) (xs : BitString) :
    Function.update (store low high) (solverEmbedding k i) xs=store low (Function.update high i xs) := by
  apply store_ext
  · funext j;simp only [Function.comp_def,Function.update_of_ne (low_solver_ne k j i),store_low]
  · funext j;simp only [Function.comp_def,Function.update_apply,(solverEmbedding k).injective.eq_iff,store_solver]

lemma lift_executes {k : ℕ} (B : OracleBlock 35) (g : BitString → ℕ) (s t : Store 35) (c : ℕ)
    (h : B.Executes g s t c) :
    (rename B (lowEmbedding k)).Executes g (lifted s) (lifted t) c := by
  apply rename_executes_to B (lowEmbedding k) g h
  · funext i;exact store_low (k:=k) _ (fun _=>[]) i
  · funext i;exact store_low (k:=k) _ (fun _=>[]) i
  · intro i hi
    have hnot : ¬i.val<36 := by
      intro hsmall
      exact hi ⟨i.val,hsmall⟩ (Fin.ext rfl)
    simp [lifted,store,hnot]

noncomputable def load (k : ℕ) : OracleBlock (k+36) :=
  moveOn (lowEmbedding k 0) (solverEmbedding k 0) (lowEmbedding k 24)
    (low_solver_ne _ _ _) ((lowEmbedding k).injective.ne (by decide : (0:Fin 36)≠24)) (solver_low_ne _ _ _)
noncomputable def unload (k : ℕ) : OracleBlock (k+36) :=
  moveOn (solverEmbedding k 0) (lowEmbedding k 0) (lowEmbedding k 24)
    (solver_low_ne _ _ _) (solver_low_ne _ _ _) ((lowEmbedding k).injective.ne (by decide : (0:Fin 36)≠24))
noncomputable def program {k : ℕ} (S : OracleBlock k) : OracleBlock (k+36) :=
  seq (load k) (seq (rename S (solverEmbedding k)) (unload k))
noncomputable def time (p : Polynomial ℕ) : Polynomial ℕ := 7*p+12*X+14

lemma load_executes (k : ℕ) (g : BitString → ℕ) (low : Store 35) (h24 : low 24=[]) :
    (load k).Executes g (lifted low)
      (store (Function.update low 0 []) (Function.update (fun _ : Fin (k+1)=>[]) 0 (low 0))) (6*(low 0).length+5) := by
  have h := moveOn_executes g (lowEmbedding k 0) (solverEmbedding k 0) (lowEmbedding k 24)
    (low_solver_ne _ _ _) ((lowEmbedding k).injective.ne (by decide : (0:Fin 36)≠24)) (solver_low_ne _ _ _)
    (lifted low) (by simpa only [lifted,store_low] using h24)
  simpa only [lifted,store_low,store_solver,List.append_nil,update_solver,update_low] using h

lemma unload_executes (k : ℕ) (g : BitString → ℕ) (low : Store 35) (xs : BitString)
    (h24 : low 24=[]) (h0 : low 0=[]) :
    (unload k).Executes g (store low (Function.update (fun _ : Fin (k+1)=>[]) 0 xs))
      (lifted (Function.update low 0 xs)) (6*xs.length+5) := by
  have h := moveOn_executes g (solverEmbedding k 0) (lowEmbedding k 0) (lowEmbedding k 24)
    (solver_low_ne _ _ _) (solver_low_ne _ _ _) ((lowEmbedding k).injective.ne (by decide : (0:Fin 36)≠24))
    (store low (Function.update (fun _ : Fin (k+1)=>[]) 0 xs)) (by simpa only [store_low] using h24)
  simpa only [store_low,store_solver,Function.update_self,h0,List.append_nil,update_low,update_solver,
    Function.update_idem,Function.update_eq_self,lifted] using h


lemma lifted_initial {k : ℕ} (xs : BitString) :
    lifted (k:=k) (Function.update (fun _ : Fin 36=>[]) 0 xs)=
      Function.update (fun _ : Fin (k+37)=>[]) 0 xs := by
  funext i
  by_cases h : i.val<36
  · have he : (⟨i.val,h⟩:Fin 36)=0 ↔ i=0 := by
      constructor
      · intro h0;exact Fin.ext (congrArg (fun j : Fin 36=>j.val) h0)
      · intro h0;exact Fin.ext (congrArg (fun j : Fin (k+37)=>j.val) h0)
    simp [lifted,store,h,Function.update_apply,he]
  · have h0 : i≠0 := by intro h0;subst i;norm_num at h
    simp [lifted,store,h,h0]

theorem program_executes {k : ℕ} (S : OracleBlock k) (g : BitString → ℕ) (p : Polynomial ℕ)
    (hS : SolverSpec S g p) (C : ConstraintInput) (low : Store 35)
    (h24 : low 24=[]) (h0 : low 0=C.encode) :
    ∃c, (program S).Executes g (lifted low)
      (lifted (Function.update low 0 (RationalOracleEncoding.bits C.value))) c ∧
      c≤(time p).eval C.encode.length := by
  obtain ⟨c,hc,hcb⟩ := hS C
  have hl := load_executes k g low h24
  rw [h0] at hl
  have hw : (rename S (solverEmbedding k)).Executes g
      (store (Function.update low 0 []) (Function.update (fun _ : Fin (k+1)=>[]) 0 C.encode))
      (store (Function.update low 0 []) (Function.update (fun _ : Fin (k+1)=>[]) 0 (RationalOracleEncoding.bits C.value))) c := by
    apply rename_executes_to S (solverEmbedding k) g hc
    · funext i;exact store_solver _ _ i
    · funext i;exact store_solver _ _ i
    · intro i hi
      have hsmall : i.val<36 := by
        by_contra h
        let j : Fin (k+1) := ⟨i.val-36,by omega⟩
        apply hi j
        apply Fin.ext
        dsimp [solverEmbedding,j]
        omega
      simp [store,hsmall]
  have hu := unload_executes k g (Function.update low 0 []) (RationalOracleEncoding.bits C.value)
    (by simpa using h24) (by simp)
  simp only [Function.update_idem] at hu
  have hsize := hc.stack_bound (show ∀i,(Function.update (fun _ : Fin (k+1)=>[]) 0 C.encode i).length≤C.encode.length by
    intro i;simp only [Function.update_apply];split_ifs <;> simp) (0:Fin (k+1))
  change (RationalOracleEncoding.bits C.value).length≤C.encode.length+c at hsize
  refine ⟨_,seq_executes _ _ g hl (seq_executes _ _ g hw hu),?_⟩
  simp only [time,eval_add,eval_mul,eval_ofNat,eval_X]
  omega
end HiddenCircuits.Circuit.Runtime.NativeConstraintCall
