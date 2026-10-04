import HiddenCircuits.DH.Runtime.PairCheckModel

/-! Literal read primitives for fixed-register twin and pendant checking. -/
namespace HiddenCircuits.DH.Runtime.PairCheck.TestRuntime
open Complexity Complexity.OracleBlock

/-- Ports 0–4 are read-only n, matrix, marks, u, v; port 5 is the result.
Ports 6/7 are the scan index and clock; 8–18 are singleton flags; 19–22 are scratch. -/
def state (n u v x : ℕ) (payload marks output clock : BitString) (f : Fin 11 → BitString) : Store 22 :=
  ![List.replicate n true,payload,marks,List.replicate u true,List.replicate v true,output,
    List.replicate x true,clock,f 0,f 1,f 2,f 3,f 4,f 5,f 6,f 7,f 8,f 9,f 10,[],[],[],[]]

def flags (acc au av eq edge ax eu ev vx ux tmp : BitString) : Fin 11 → BitString :=
  ![acc,au,av,eq,edge,ax,eu,ev,vx,ux,tmp]

def readUEmbedding : Fin 7 ↪ Fin 23 where
  toFun i := ![2,3,9,19,20,21,22] i
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
noncomputable def readU : OracleBlock 22 := GraphReduction.Runtime.listLookupOn readUEmbedding

lemma readU_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (alive : Vector Bool n) (u v : Fin n) (x : ℕ) (output clock : BitString)
    (f : Fin 11 → BitString) (hf : f 1=[]) :
    ∃t, readU.Executes g (state n u.val v.val x G.bits (liveBits alive) output clock f)
      (state n u.val v.val x G.bits (liveBits alive) output clock
        (Function.update f 1 [alive[u.val]])) t ∧ t≤100*(n+1)^2 := by
  obtain ⟨t,ht,hb⟩ := GraphReduction.Runtime.listLookupOn_executes readUEmbedding g
    (state n u.val v.val x G.bits (liveBits alive) output clock f) (liveWords alive) u.val
    (by funext i;fin_cases i <;> simp [state,readUEmbedding,GraphReduction.Runtime.lookupStore,liveBits,hf])
  refine ⟨t,?_,?_⟩
  · convert ht using 1
    funext i;fin_cases i <;> simp [state,readUEmbedding,liveWords_get,hf]
  · change t≤GraphReduction.Runtime.lookupBound (liveBits alive).length u.val at hb
    rw [liveBits_length] at hb
    unfold GraphReduction.Runtime.lookupBound at hb
    have hm := Nat.mul_le_mul_left n u.isLt.le
    nlinarith [u.isLt]

lemma readU_queryFree : readU.QueryFree := GraphReduction.Runtime.listLookupOn_queryFree _

def readVEmbedding : Fin 7 ↪ Fin 23 where
  toFun i := ![2,4,10,19,20,21,22] i
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
noncomputable def readV : OracleBlock 22 := GraphReduction.Runtime.listLookupOn readVEmbedding

lemma readV_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (alive : Vector Bool n) (u v : Fin n) (x : ℕ) (output clock : BitString)
    (f : Fin 11 → BitString) (hf : f 2=[]) :
    ∃t, readV.Executes g (state n u.val v.val x G.bits (liveBits alive) output clock f)
      (state n u.val v.val x G.bits (liveBits alive) output clock
        (Function.update f 2 [alive[v.val]])) t ∧ t≤100*(n+1)^2 := by
  obtain ⟨t,ht,hb⟩ := GraphReduction.Runtime.listLookupOn_executes readVEmbedding g
    (state n u.val v.val x G.bits (liveBits alive) output clock f) (liveWords alive) v.val
    (by funext i;fin_cases i <;> simp [state,readVEmbedding,GraphReduction.Runtime.lookupStore,liveBits,hf])
  refine ⟨t,?_,?_⟩
  · convert ht using 1
    funext i;fin_cases i <;> simp [state,readVEmbedding,liveWords_get,hf]
  · change t≤GraphReduction.Runtime.lookupBound (liveBits alive).length v.val at hb
    rw [liveBits_length] at hb
    unfold GraphReduction.Runtime.lookupBound at hb
    have hm := Nat.mul_le_mul_left n v.isLt.le
    nlinarith [v.isLt]

lemma readV_queryFree : readV.QueryFree := GraphReduction.Runtime.listLookupOn_queryFree _

def readXEmbedding : Fin 7 ↪ Fin 23 where
  toFun i := ![2,6,13,19,20,21,22] i
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
noncomputable def readX : OracleBlock 22 := GraphReduction.Runtime.listLookupOn readXEmbedding

lemma readX_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (alive : Vector Bool n) (u v : Fin n) (x : Fin n) (output clock : BitString)
    (f : Fin 11 → BitString) (hf : f 5=[]) :
    ∃t, readX.Executes g (state n u.val v.val x.val G.bits (liveBits alive) output clock f)
      (state n u.val v.val x.val G.bits (liveBits alive) output clock
        (Function.update f 5 [alive[x.val]])) t ∧ t≤100*(n+1)^2 := by
  obtain ⟨t,ht,hb⟩ := GraphReduction.Runtime.listLookupOn_executes readXEmbedding g
    (state n u.val v.val x.val G.bits (liveBits alive) output clock f) (liveWords alive) x.val
    (by funext i;fin_cases i <;> simp [state,readXEmbedding,GraphReduction.Runtime.lookupStore,liveBits,hf])
  refine ⟨t,?_,?_⟩
  · convert ht using 1
    funext i;fin_cases i <;> simp [state,readXEmbedding,liveWords_get,hf]
  · change t≤GraphReduction.Runtime.lookupBound (liveBits alive).length x.val at hb
    rw [liveBits_length] at hb
    unfold GraphReduction.Runtime.lookupBound at hb
    have hm := Nat.mul_le_mul_left n x.isLt.le
    nlinarith [x.isLt]

lemma readX_queryFree : readX.QueryFree := GraphReduction.Runtime.listLookupOn_queryFree _

def compareUVEmbedding : Fin 6 ↪ Fin 23 where
  toFun i := ![3,4,11,19,20,21] i
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
noncomputable def compareUV : OracleBlock 22 := GraphVerifier.Runtime.readLengthOn compareUVEmbedding

lemma compareUV_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (alive : Vector Bool n) (u v : Fin n) (x : ℕ) (output clock : BitString)
    (f : Fin 11 → BitString) (hf : f 3=[]) :
    ∃t, compareUV.Executes g (state n u.val v.val x G.bits (liveBits alive) output clock f)
      (state n u.val v.val x G.bits (liveBits alive) output clock
        (Function.update f 3 [decide (u=v)])) t ∧ t≤100*(n+1)^2 := by
  obtain ⟨t,ht,hb⟩ := GraphVerifier.Runtime.readLengthOn_executes compareUVEmbedding g
    (state n u.val v.val x G.bits (liveBits alive) output clock f)
    (List.replicate u.val true) (List.replicate v.val true)
    (by funext i;fin_cases i <;> simp [state,compareUVEmbedding,GraphVerifier.Runtime.readLengthStore,hf])
  refine ⟨t,?_,?_⟩
  · convert ht using 1
    funext i;fin_cases i <;> simp [state,compareUVEmbedding,hf,Fin.ext_iff]
  · simp only [List.length_replicate] at hb
    nlinarith [u.isLt,v.isLt]

lemma compareUV_queryFree : compareUV.QueryFree := GraphVerifier.Runtime.readLengthOn_queryFree _

def compareXUEmbedding : Fin 6 ↪ Fin 23 where
  toFun i := ![6,3,14,19,20,21] i
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
noncomputable def compareXU : OracleBlock 22 := GraphVerifier.Runtime.readLengthOn compareXUEmbedding

lemma compareXU_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (alive : Vector Bool n) (u v : Fin n) (x : Fin n) (output clock : BitString)
    (f : Fin 11 → BitString) (hf : f 6=[]) :
    ∃t, compareXU.Executes g (state n u.val v.val x.val G.bits (liveBits alive) output clock f)
      (state n u.val v.val x.val G.bits (liveBits alive) output clock
        (Function.update f 6 [decide (x=u)])) t ∧ t≤100*(n+1)^2 := by
  obtain ⟨t,ht,hb⟩ := GraphVerifier.Runtime.readLengthOn_executes compareXUEmbedding g
    (state n u.val v.val x.val G.bits (liveBits alive) output clock f)
    (List.replicate x.val true) (List.replicate u.val true)
    (by funext i;fin_cases i <;> simp [state,compareXUEmbedding,GraphVerifier.Runtime.readLengthStore,hf])
  refine ⟨t,?_,?_⟩
  · convert ht using 1
    funext i;fin_cases i <;> simp [state,compareXUEmbedding,hf,Fin.ext_iff]
  · simp only [List.length_replicate] at hb
    nlinarith [x.isLt,u.isLt]

lemma compareXU_queryFree : compareXU.QueryFree := GraphVerifier.Runtime.readLengthOn_queryFree _

def compareXVEmbedding : Fin 6 ↪ Fin 23 where
  toFun i := ![6,4,15,19,20,21] i
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
noncomputable def compareXV : OracleBlock 22 := GraphVerifier.Runtime.readLengthOn compareXVEmbedding

lemma compareXV_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (alive : Vector Bool n) (u v : Fin n) (x : Fin n) (output clock : BitString)
    (f : Fin 11 → BitString) (hf : f 7=[]) :
    ∃t, compareXV.Executes g (state n u.val v.val x.val G.bits (liveBits alive) output clock f)
      (state n u.val v.val x.val G.bits (liveBits alive) output clock
        (Function.update f 7 [decide (x=v)])) t ∧ t≤100*(n+1)^2 := by
  obtain ⟨t,ht,hb⟩ := GraphVerifier.Runtime.readLengthOn_executes compareXVEmbedding g
    (state n u.val v.val x.val G.bits (liveBits alive) output clock f)
    (List.replicate x.val true) (List.replicate v.val true)
    (by funext i;fin_cases i <;> simp [state,compareXVEmbedding,GraphVerifier.Runtime.readLengthStore,hf])
  refine ⟨t,?_,?_⟩
  · convert ht using 1
    funext i;fin_cases i <;> simp [state,compareXVEmbedding,hf,Fin.ext_iff]
  · simp only [List.length_replicate] at hb
    nlinarith [x.isLt,v.isLt]

lemma compareXV_queryFree : compareXV.QueryFree := GraphVerifier.Runtime.readLengthOn_queryFree _

def readVUEmbedding : Fin 9 ↪ Fin 23 where
  toFun i := ![0,4,3,1,12,19,20,21,22] i
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
noncomputable def readVU : OracleBlock 22 := GraphVerifier.Runtime.matrixLookupOn readVUEmbedding

lemma readVU_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (alive : Vector Bool n) (u v : Fin n) (x : ℕ) (output clock : BitString)
    (f : Fin 11 → BitString) (hf : f 4=[]) :
    ∃t, readVU.Executes g (state n u.val v.val x G.bits (liveBits alive) output clock f)
      (state n u.val v.val x G.bits (liveBits alive) output clock
        (Function.update f 4 [G.edge v u])) t ∧ t≤100*(n+1)^2 := by
  have ht := GraphVerifier.Runtime.matrixLookupOn_executes readVUEmbedding g
    (state n u.val v.val x G.bits (liveBits alive) output clock f) n v.val u.val G.bits
    (by funext i;fin_cases i <;> simp [state,readVUEmbedding,GraphVerifier.Runtime.matrixStore,hf])
  refine ⟨GraphVerifier.Runtime.matrixLookupCost n v.val u.val G.bits,?_,?_⟩
  · convert ht using 1
    funext i;fin_cases i <;> simp [state,readVUEmbedding,matrix_bit,hf]
  · have hb := GraphVerifier.Runtime.matrixLookupCost_in_range n v.val u.val G.bits v.isLt u.isLt
    nlinarith

lemma readVU_queryFree : readVU.QueryFree := GraphVerifier.Runtime.matrixLookupOn_queryFree _

def readVXEmbedding : Fin 9 ↪ Fin 23 where
  toFun i := ![0,4,6,1,16,19,20,21,22] i
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
noncomputable def readVX : OracleBlock 22 := GraphVerifier.Runtime.matrixLookupOn readVXEmbedding

lemma readVX_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (alive : Vector Bool n) (u v : Fin n) (x : Fin n) (output clock : BitString)
    (f : Fin 11 → BitString) (hf : f 8=[]) :
    ∃t, readVX.Executes g (state n u.val v.val x.val G.bits (liveBits alive) output clock f)
      (state n u.val v.val x.val G.bits (liveBits alive) output clock
        (Function.update f 8 [G.edge v x])) t ∧ t≤100*(n+1)^2 := by
  have ht := GraphVerifier.Runtime.matrixLookupOn_executes readVXEmbedding g
    (state n u.val v.val x.val G.bits (liveBits alive) output clock f) n v.val x.val G.bits
    (by funext i;fin_cases i <;> simp [state,readVXEmbedding,GraphVerifier.Runtime.matrixStore,hf])
  refine ⟨GraphVerifier.Runtime.matrixLookupCost n v.val x.val G.bits,?_,?_⟩
  · convert ht using 1
    funext i;fin_cases i <;> simp [state,readVXEmbedding,matrix_bit,hf]
  · have hb := GraphVerifier.Runtime.matrixLookupCost_in_range n v.val x.val G.bits v.isLt x.isLt
    nlinarith

lemma readVX_queryFree : readVX.QueryFree := GraphVerifier.Runtime.matrixLookupOn_queryFree _

def readUXEmbedding : Fin 9 ↪ Fin 23 where
  toFun i := ![0,3,6,1,17,19,20,21,22] i
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
noncomputable def readUX : OracleBlock 22 := GraphVerifier.Runtime.matrixLookupOn readUXEmbedding

lemma readUX_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (alive : Vector Bool n) (u v : Fin n) (x : Fin n) (output clock : BitString)
    (f : Fin 11 → BitString) (hf : f 9=[]) :
    ∃t, readUX.Executes g (state n u.val v.val x.val G.bits (liveBits alive) output clock f)
      (state n u.val v.val x.val G.bits (liveBits alive) output clock
        (Function.update f 9 [G.edge u x])) t ∧ t≤100*(n+1)^2 := by
  have ht := GraphVerifier.Runtime.matrixLookupOn_executes readUXEmbedding g
    (state n u.val v.val x.val G.bits (liveBits alive) output clock f) n u.val x.val G.bits
    (by funext i;fin_cases i <;> simp [state,readUXEmbedding,GraphVerifier.Runtime.matrixStore,hf])
  refine ⟨GraphVerifier.Runtime.matrixLookupCost n u.val x.val G.bits,?_,?_⟩
  · convert ht using 1
    funext i;fin_cases i <;> simp [state,readUXEmbedding,matrix_bit,hf]
  · have hb := GraphVerifier.Runtime.matrixLookupCost_in_range n u.val x.val G.bits u.isLt x.isLt
    nlinarith

lemma readUX_queryFree : readUX.QueryFree := GraphVerifier.Runtime.matrixLookupOn_queryFree _

end HiddenCircuits.DH.Runtime.PairCheck.TestRuntime
