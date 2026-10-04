import HiddenCircuits.Complexity.GraphVerifier.UnaryProduct

/-! Read-only row-major adjacency lookup by actual finite bit-stack programs.
The unary multiplication, offset addition, indexed scan, and cleanup are all
charged instructions. No arbitrary indexing function occurs in the code. -/
namespace HiddenCircuits.Complexity.GraphVerifier.Runtime
open OracleBlock OracleMachine

/-- Ports 0--3 are the read-only header, row, column, and payload. Port 4 is the
optional bit result; ports 5--8 are empty on entry and exit. -/
def matrixStore (header row col payload output index counter tempData tempIndex : BitString) : Store 8 := fun i =>
  if i.val=0 then header else if i.val=1 then row else if i.val=2 then col
  else if i.val=3 then payload else if i.val=4 then output else if i.val=5 then index
  else if i.val=6 then counter else if i.val=7 then tempData else tempIndex

noncomputable def matrixCopyRow : OracleBlock 8 := copyOn 1 6 7 (by decide) (by decide) (by decide)
noncomputable def matrixCopyCol : OracleBlock 8 := copyOn 2 5 7 (by decide) (by decide) (by decide)

def matrixProductEmbedding : Fin 4 ↪ Fin 9 where
  toFun i := if i.val=0 then 0 else if i.val=1 then 6 else if i.val=2 then 5 else 7
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

noncomputable def matrixProduct : OracleBlock 8 := rename repeatCopyBlock matrixProductEmbedding

def matrixReadEmbedding : Fin 5 ↪ Fin 9 where
  toFun i := if i.val=0 then 3 else if i.val=1 then 5 else if i.val=2 then 4 else if i.val=3 then 7 else 8
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

noncomputable def matrixRead : OracleBlock 8 := lookupOn matrixReadEmbedding

noncomputable def matrixLookup : OracleBlock 8 :=
  seq matrixCopyRow (seq matrixCopyCol (seq matrixProduct (seq matrixRead (clear 5))))

def matrixLookupCost (n row col : ℕ) (payload : BitString) : ℕ :=
  (5*row+2)+(5*col+2)+(row*(5*n+4)+1)+
    Lookup.cost payload (List.replicate (col+n*row) true)+(col+n*row+1)+8

lemma matrixLookupCost_bound (n row col : ℕ) (payload : BitString) :
    matrixLookupCost n row col payload ≤ 14*n*row+9*row+14*col+20 := by
  have h := Lookup.cost_bound payload (List.replicate (col+n*row) true)
  simp only [List.length_replicate] at h
  unfold matrixLookupCost
  nlinarith

/-- Preserve unary n, row, column, and payload; clear every local work stack;
return the exact optional row-major bit, including out-of-range behavior. -/
theorem matrixLookup_executes (g : BitString → ℕ) (n row col : ℕ) (payload : BitString) :
    matrixLookup.Executes g
      (matrixStore (List.replicate n true) (List.replicate row true) (List.replicate col true) payload [] [] [] [] [])
      (matrixStore (List.replicate n true) (List.replicate row true) (List.replicate col true) payload
        (payload[col+n*row]?.toList) [] [] [] []) (matrixLookupCost n row col payload) := by
  have hrow : matrixCopyRow.Executes g
      (matrixStore (List.replicate n true) (List.replicate row true) (List.replicate col true) payload [] [] [] [] [])
      (matrixStore (List.replicate n true) (List.replicate row true) (List.replicate col true) payload [] []
        (List.replicate row true) [] []) (5*row+2) := by
    convert copyOn_executes g (1 : Fin 9) 6 7 (by decide) (by decide) (by decide)
      (matrixStore (List.replicate n true) (List.replicate row true) (List.replicate col true) payload [] [] [] [] []) rfl using 1
    · funext i; fin_cases i <;> simp [matrixStore]
    · simp [matrixStore]
  have hcol : matrixCopyCol.Executes g
      (matrixStore (List.replicate n true) (List.replicate row true) (List.replicate col true) payload [] []
        (List.replicate row true) [] [])
      (matrixStore (List.replicate n true) (List.replicate row true) (List.replicate col true) payload []
        (List.replicate col true) (List.replicate row true) [] []) (5*col+2) := by
    convert copyOn_executes g (2 : Fin 9) 5 7 (by decide) (by decide) (by decide)
      (matrixStore (List.replicate n true) (List.replicate row true) (List.replicate col true) payload [] []
        (List.replicate row true) [] []) rfl using 1
    · funext i; fin_cases i <;> simp [matrixStore]
    · simp [matrixStore]
  have hp : matrixProduct.Executes g
      (matrixStore (List.replicate n true) (List.replicate row true) (List.replicate col true) payload []
        (List.replicate col true) (List.replicate row true) [] [])
      (matrixStore (List.replicate n true) (List.replicate row true) (List.replicate col true) payload []
        (List.replicate (col+n*row) true) [] [] []) (row*(5*n+4)+1) := by
    have h := repeatCopy_execution g (List.replicate n true) (List.replicate row true) (List.replicate col true)
    rw [List.length_replicate,repeatPrefix_unary,List.length_replicate] at h
    have he : row*n+col=col+n*row := by ring
    rw [he] at h
    apply rename_executes_to repeatCopyBlock matrixProductEmbedding g h
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
    · intro j hj
      fin_cases j
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact False.elim (hj 2 rfl)
      · exact False.elim (hj 1 rfl)
      · rfl
      · rfl
  have hr : matrixRead.Executes g
      (matrixStore (List.replicate n true) (List.replicate row true) (List.replicate col true) payload []
        (List.replicate (col+n*row) true) [] [] [])
      (matrixStore (List.replicate n true) (List.replicate row true) (List.replicate col true) payload
        (payload[col+n*row]?.toList) (List.replicate (col+n*row) true) [] [] [])
      (Lookup.cost payload (List.replicate (col+n*row) true)) := by
    apply lookupOn_executes matrixReadEmbedding g _ _ payload (List.replicate (col+n*row) true)
    · funext i; fin_cases i <;> rfl
    · simp only [List.length_replicate]
      funext i; fin_cases i <;> rfl
    · intro j hj
      fin_cases j
      · rfl
      · rfl
      · rfl
      · rfl
      · exact False.elim (hj 2 rfl)
      · rfl
      · rfl
      · rfl
      · rfl
  have hc : (clear (5 : Fin 9)).Executes g
      (matrixStore (List.replicate n true) (List.replicate row true) (List.replicate col true) payload
        (payload[col+n*row]?.toList) (List.replicate (col+n*row) true) [] [] [])
      (matrixStore (List.replicate n true) (List.replicate row true) (List.replicate col true) payload
        (payload[col+n*row]?.toList) [] [] [] []) (col+n*row+1) := by
    convert clear_executes g (5 : Fin 9)
      (matrixStore (List.replicate n true) (List.replicate row true) (List.replicate col true) payload
        (payload[col+n*row]?.toList) (List.replicate (col+n*row) true) [] [] []) using 1
    · funext i; fin_cases i <;> rfl
    · simp [matrixStore]
  have h := seq_executes _ _ g hrow (seq_executes _ _ g hcol (seq_executes _ _ g hp (seq_executes _ _ g hr hc)))
  convert h using 1 <;> unfold matrixLookupCost <;> omega

lemma matrixLookup_queryFree : matrixLookup.QueryFree := by
  have hrow : matrixCopyRow.QueryFree := copyOn_queryFree _ _ _ _ _ _
  have hcol : matrixCopyCol.QueryFree := copyOn_queryFree _ _ _ _ _ _
  have hp : matrixProduct.QueryFree := rename_queryFree _ _ repeatCopy_queryFree
  have hr : matrixRead.QueryFree := lookupOn_queryFree _
  exact seq_queryFree _ _ hrow (seq_queryFree _ _ hcol (seq_queryFree _ _ hp (seq_queryFree _ _ hr (clear_queryFree _))))

/-- Explicit quadratic charge in the usual row/column range. -/
lemma matrixLookupCost_in_range (n row col : ℕ) (payload : BitString) (hi : row<n) (hj : col<n) :
    matrixLookupCost n row col payload ≤ 14*n^2+23*n+20 := by
  have h := matrixLookupCost_bound n row col payload
  have hm := Nat.mul_le_mul_left (14*n) hi.le
  nlinarith

noncomputable def matrixLookupOn {k : ℕ} (φ : Fin 9 ↪ Fin (k+1)) : OracleBlock k := rename matrixLookup φ

/-- Arbitrary-stack reuse changes only the result port. The four sources and
all external stacks are preserved, and local work cells return to empty. -/
theorem matrixLookupOn_executes {k : ℕ} (φ : Fin 9 ↪ Fin (k+1)) (g : BitString → ℕ)
    (s : Store k) (n row col : ℕ) (payload : BitString)
    (hs : s ∘ φ=matrixStore (List.replicate n true) (List.replicate row true)
      (List.replicate col true) payload [] [] [] [] []) :
    (matrixLookupOn φ).Executes g s (Function.update s (φ 4) (payload[col+n*row]?.toList))
      (matrixLookupCost n row col payload) := by
  apply rename_executes_to matrixLookup φ g (matrixLookup_executes g n row col payload) hs
  · have he : (Function.update s (φ 4) (payload[col+n*row]?.toList)) ∘ φ =
        Function.update (s ∘ φ) 4 (payload[col+n*row]?.toList) := by
      funext j
      simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext j; fin_cases j <;> rfl
  · intro j hj
    exact Function.update_of_ne (hj 4).symm _ _

lemma matrixLookupOn_queryFree {k : ℕ} (φ : Fin 9 ↪ Fin (k+1)) : (matrixLookupOn φ).QueryFree :=
  rename_queryFree _ _ matrixLookup_queryFree

end HiddenCircuits.Complexity.GraphVerifier.Runtime
