import HiddenCircuits.Circuit.Runtime.CircuitMetadata
import HiddenCircuits.Complexity.UnaryArithmetic

/-! Count the actual sampled constraints and physically
compute the unary geometric interpolation degree. -/
namespace HiddenCircuits.Circuit.Runtime.SampleDimensions
open HiddenCircuits.Complexity OracleBlock Polynomial

lemma sampled_occurrences {n : ℕ} (w : List (ConstraintGate n)) (r s : ℕ) :
    deltaOccurrences (sampledConstraintCircuit w r s)=2*r*forbidOccurrences w+2*s*signOccurrences w := by
  induction w with
  | nil => simp [deltaOccurrences,sampledConstraintCircuit,forbidOccurrences,signOccurrences,firstMarks,secondMarks]
  | cons a w ih =>
    cases a <;> simp_all [deltaOccurrences,sampledConstraintCircuit,ConstraintGate.sampleWord,DeltaGate.mark,
      forbidOccurrences,signOccurrences,ConstraintGate.spectral,firstMarks,secondMarks,List.map_append,List.sum_append]
    all_goals ring

def store (f z r s clock out : ℕ) : Store 7 := fun i =>
  List.replicate (if i.val=0 then f else if i.val=1 then z else if i.val=2 then r else if i.val=3 then s
    else if i.val=4 then clock else if i.val=6 then out else 0) true

def countPort (second : Bool) : Fin 8 := if second then 1 else 0
def indexPort (second : Bool) : Fin 8 := if second then 3 else 2
def count (second : Bool) (f z : ℕ) : ℕ := if second then z else f
def index (second : Bool) (r s : ℕ) : ℕ := if second then s else r
noncomputable def multiply (second : Bool) : OracleBlock 7 :=
  seq (copyOn (indexPort second) 4 7 (by cases second <;> decide) (by cases second <;> decide) (by decide))
    (repeatCopy 4 (countPort second) 6 7 (by cases second <;> decide) (by cases second <;> decide) (by decide))
noncomputable def quadruple : OracleBlock 7 := seq (copyOn 6 4 7 (by decide) (by decide) (by decide))
  (seq (clear 6) (repeatPrepend 4 6 [true,true,true,true]))
noncomputable def program : OracleBlock 7 := seq (multiply false) (seq (multiply true) quadruple)
noncomputable def time : Polynomial ℕ := 100*(X+1)^2

lemma multiply_executes (g : BitString → ℕ) (second : Bool) (f z r s out : ℕ) :
    (multiply second).Executes g (store f z r s 0 out)
      (store f z r s 0 (index second r s*count second f z+out))
      ((5*count second f z+9)*index second r s+5) := by
  have hc : (copyOn (indexPort second) (4:Fin 8) 7 (by cases second <;> decide) (by cases second <;> decide) (by decide)).Executes g
      (store f z r s 0 out) (store f z r s (index second r s) out) (5*index second r s+2) := by
    convert copyOn_executes g (indexPort second) (4:Fin 8) 7 (by cases second <;> decide) (by cases second <;> decide) (by decide)
      (store f z r s 0 out) rfl using 1
    · funext i;cases second <;> fin_cases i <;> simp [store,indexPort,index]
    · cases second <;> simp [store,indexPort,index]
  have hm : (repeatCopy (4:Fin 8) (countPort second) 6 7 (by cases second <;> decide) (by cases second <;> decide) (by decide)).Executes g
      (store f z r s (index second r s) out) (store f z r s 0 (index second r s*count second f z+out))
      ((5*count second f z+4)*index second r s+1) := by
    convert unaryMultiply_executes g (4:Fin 8) (countPort second) 6 7 (by cases second <;> decide) (by decide) (by decide)
      (by cases second <;> decide) (by cases second <;> decide) (by decide)
      (store f z r s (index second r s) out) (index second r s) (count second f z) rfl
      (by cases second <;> rfl) rfl using 1
    funext i;fin_cases i <;> simp [store,workStore,←List.replicate_add]
  convert seq_executes _ _ g hc hm using 1 <;> ring

lemma quadruple_executes (g : BitString → ℕ) (f z r s out : ℕ) :
    quadruple.Executes g (store f z r s 0 out) (store f z r s 0 (4*out)) (21*out+8) := by
  have hc : (copyOn (6:Fin 8) 4 7 (by decide) (by decide) (by decide)).Executes g
      (store f z r s 0 out) (store f z r s out out) (5*out+2) := by
    convert copyOn_executes g (6:Fin 8) 4 7 (by decide) (by decide) (by decide) (store f z r s 0 out) rfl using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  have he : (clear (6:Fin 8)).Executes g (store f z r s out out) (store f z r s out 0) (out+1) := by
    convert clear_executes g (6:Fin 8) (store f z r s out out) using 1
    · funext i;fin_cases i <;> rfl
    · simp [store]
  have hflat : (List.replicate out [true,true,true,true]).flatten=List.replicate (4*out) true := by
    clear hc he
    induction out with
    | zero => rfl
    | succ out ih => simp only [List.replicate_succ,List.flatten_cons,ih];rw [Nat.mul_succ,Nat.add_comm (4*out),List.replicate_add];rfl
  have hr : (repeatPrepend (4:Fin 8) 6 [true,true,true,true]).Executes g
      (store f z r s out 0) (store f z r s 0 (4*out)) (15*out+1) := by
    convert repeatPrepend_executes g (4:Fin 8) 6 (by decide) [true,true,true,true] (store f z r s out 0) using 1
    · funext i;fin_cases i <;> simp [store,hflat]
    · simp [store]
  convert seq_executes _ _ g hc (seq_executes _ _ g he hr) using 1 <;> omega

theorem program_executes (g : BitString → ℕ) (f z r s : ℕ) :
    ∃c,program.Executes g (store f z r s 0 0) (store f z r s 0 (4*r*f+4*s*z)) c ∧ c≤time.eval (f+z+r+s) := by
  have h1:=multiply_executes g false f z r s 0
  have h2:=multiply_executes g true f z r s (r*f)
  have h3:=quadruple_executes g f z r s (s*z+r*f)
  simp only [index,count,Bool.false_eq_true,if_false,if_true,Nat.add_zero] at h1 h2
  have he : 4*(s*z+r*f)=4*r*f+4*s*z := by ring
  rw [he] at h3
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 h3),?_⟩
  simp only [time,eval_mul,eval_pow,eval_add,eval_X,eval_ofNat,eval_one]
  nlinarith [Nat.zero_le (f*z),Nat.zero_le (f*s),Nat.zero_le (z*r),Nat.zero_le (r*s)]

lemma multiply_queryFree (b : Bool) : (multiply b).QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (repeatCopy_queryFree _ _ _ _ _ _ _)
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (multiply_queryFree _) (seq_queryFree _ _ (multiply_queryFree _)
  (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (clear_queryFree _) (repeatPrepend_queryFree _ _ _))))
noncomputable def on {k : ℕ} (φ : Fin 8 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 8 ↪ Fin (k+1)) (g : BitString → ℕ) (st : Store k)
    (f z r s : ℕ) (hs : st∘φ=store f z r s 0 0) :
    ∃c,(on φ).Executes g st (Function.update st (φ 6) (List.replicate (4*r*f+4*s*z) true)) c ∧
      c≤time.eval (f+z+r+s) := by
  obtain ⟨c,hc,hb⟩:=program_executes g f z r s
  refine ⟨c,?_,hb⟩
  apply rename_executes_to _ φ g hc hs
  · funext i
    have hi:=congrFun hs i
    change st (φ i)=_ at hi
    simp only [Function.comp_def,Function.update_apply,φ.injective.eq_iff,hi]
    fin_cases i <;> rfl
  · intro i hi;simp only [Function.update_of_ne (hi 6).symm]
lemma on_queryFree {k : ℕ} (φ : Fin 8 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ program_queryFree

theorem circuit_executes (g : BitString → ℕ) {n : ℕ} (w : List (ConstraintGate n)) (r s : ℕ) :
    ∃c,program.Executes g (store (forbidOccurrences w) (signOccurrences w) r s 0 0)
      (store (forbidOccurrences w) (signOccurrences w) r s 0 (2*deltaOccurrences (sampledConstraintCircuit w r s))) c ∧
      c≤time.eval (forbidOccurrences w+signOccurrences w+r+s) := by
  rw [sampled_occurrences]
  have he : 2*(2*r*forbidOccurrences w+2*s*signOccurrences w)=4*r*forbidOccurrences w+4*s*signOccurrences w := by ring
  rw [he]
  exact program_executes g _ _ r s
end HiddenCircuits.Circuit.Runtime.SampleDimensions
