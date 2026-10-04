import HiddenCircuits.GraphReduction.Runtime.ListLookup
import HiddenCircuits.Complexity.GraphVerifier.MatrixLookup

/-! Row-major lookup in an actual encoded word matrix. Unary offset
arithmetic, lookup, and cleanup all execute as finite instructions. -/
namespace HiddenCircuits.Approximation.Initialization.WordMatrixLookup
open Complexity Complexity.OracleBlock GraphVerifier.Runtime

def state (n i j : ℕ) (data out index counter tmp : BitString) : Store 12 := fun r =>
  if r.val=0 then List.replicate n true else if r.val=1 then List.replicate i true
  else if r.val=2 then List.replicate j true else if r.val=3 then data else if r.val=4 then out
  else if r.val=5 then index else if r.val=6 then counter else if r.val=7 then tmp else []

def productPorts : Fin 4 ↪ Fin 13 where
  toFun r := if r.val=0 then 0 else if r.val=1 then 6 else if r.val=2 then 5 else 7
  inj' := by decide +kernel
def lookupPorts : Fin 7 ↪ Fin 13 where
  toFun r := if r.val=0 then 3 else if r.val=1 then 5 else if r.val=2 then 4
    else ⟨r.val+5,by omega⟩
  inj' := by decide +kernel

noncomputable def program : OracleBlock 12 :=
  seq (copyOn 1 6 7 (by decide) (by decide) (by decide))
    (seq (copyOn 2 5 7 (by decide) (by decide) (by decide))
      (seq (rename repeatCopyBlock productPorts)
        (seq (GraphReduction.Runtime.listLookupOn lookupPorts) (clear 5))))

def timeBound (n i j L : ℕ) : ℕ := (5*i+2)+(5*j+2)+(i*(5*n+4)+1)+
  GraphReduction.Runtime.lookupBound L (j+n*i)+(j+n*i+1)+8

theorem program_executes (g : BitString → ℕ) (n i j : ℕ) (ws : List BitString) :
    ∃ t, program.Executes g (state n i j (encodeBitList ws) [] [] [] [])
      (state n i j (encodeBitList ws) (ws[j+n*i]?.getD []) [] [] []) t ∧
      t ≤ timeBound n i j (encodeBitList ws).length := by
  let D := encodeBitList ws
  let offset := List.replicate (j+n*i) true
  have h1 : (copyOn (1 : Fin 13) 6 7 (by decide) (by decide) (by decide)).Executes g
      (state n i j D [] [] [] []) (state n i j D [] [] (List.replicate i true) []) (5*i+2) := by
    convert copyOn_executes g (1 : Fin 13) 6 7 (by decide) (by decide) (by decide)
      (state n i j D [] [] [] []) rfl using 1
    · funext r;fin_cases r <;> simp [state]
    · simp [state]
  have h2 : (copyOn (2 : Fin 13) 5 7 (by decide) (by decide) (by decide)).Executes g
      (state n i j D [] [] (List.replicate i true) [])
      (state n i j D [] (List.replicate j true) (List.replicate i true) []) (5*j+2) := by
    convert copyOn_executes g (2 : Fin 13) 5 7 (by decide) (by decide) (by decide)
      (state n i j D [] [] (List.replicate i true) []) rfl using 1
    · funext r;fin_cases r <;> simp [state]
    · simp [state]
  have h3 : (rename repeatCopyBlock productPorts).Executes g
      (state n i j D [] (List.replicate j true) (List.replicate i true) [])
      (state n i j D [] offset [] []) (i*(5*n+4)+1) := by
    have hh := repeatCopy_execution g (List.replicate n true) (List.replicate i true)
      (List.replicate j true)
    rw [List.length_replicate,repeatPrefix_unary,List.length_replicate] at hh
    have he : i*n+j = j+n*i := by ring
    rw [he] at hh
    apply rename_executes_to repeatCopyBlock productPorts g hh
    · funext r;fin_cases r <;> rfl
    · funext r;fin_cases r <;> rfl
    · intro r hr
      fin_cases r
      all_goals first | rfl | exact (hr 0 rfl).elim | exact (hr 1 rfl).elim | exact (hr 2 rfl).elim | exact (hr 3 rfl).elim
  obtain ⟨a,ha,hab⟩ := GraphReduction.Runtime.listLookupOn_executes lookupPorts g
    (state n i j D [] offset [] []) ws (j+n*i)
    (by funext r;fin_cases r <;> rfl)
  have h4 : (GraphReduction.Runtime.listLookupOn lookupPorts).Executes g
      (state n i j D [] offset [] []) (state n i j D (ws[j+n*i]?.getD []) offset [] []) a := by
    convert ha using 1
    funext r;fin_cases r <;> simp [state,lookupPorts]
  have h5 : (clear (5 : Fin 13)).Executes g (state n i j D (ws[j+n*i]?.getD []) offset [] [])
      (state n i j D (ws[j+n*i]?.getD []) [] [] []) (j+n*i+1) := by
    convert clear_executes g (5 : Fin 13) _ using 1
    · funext r;fin_cases r <;> simp [state]
    · simp [state,offset]
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2
    (seq_executes _ _ g h3 (seq_executes _ _ g h4 h5))),?_⟩
  unfold timeBound
  omega

theorem timeBound_in_range {n i j L : ℕ} (hi : i < n) (hj : j < n) :
    timeBound n i j L ≤ 200*(n+L+1)^3 := by
  have hm : n*i ≤ n*n := Nat.mul_le_mul_left n hi.le
  have hm' : n*i*L ≤ n*n*L := Nat.mul_le_mul_right L hm
  have hjL : j*L ≤ n*L := Nat.mul_le_mul_right L hj.le
  unfold timeBound GraphReduction.Runtime.lookupBound
  nlinarith [Nat.zero_le (n^3),Nat.zero_le (L^3),Nat.zero_le (n*L^2)]

theorem program_queryFree : program.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (rename_queryFree _ _ repeatCopy_queryFree)
      (seq_queryFree _ _ (GraphReduction.Runtime.listLookupOn_queryFree _) (clear_queryFree _))))

noncomputable def on {k : ℕ} (φ : Fin 13 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 13 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (n i j : ℕ) (ws : List BitString) (hs : s ∘ φ = state n i j (encodeBitList ws) [] [] [] []) :
    ∃ t, (on φ).Executes g s (Function.update s (φ 4) (ws[j+n*i]?.getD [])) t ∧
      t ≤ timeBound n i j (encodeBitList ws).length := by
  obtain ⟨t,ht,hb⟩ := program_executes g n i j ws
  refine ⟨t,?_,hb⟩
  apply rename_executes_to program φ g ht hs
  · funext r
    simp only [Function.comp_apply,Function.update_apply,φ.injective.eq_iff]
    have hh := congrFun hs r
    simp only [Function.comp_apply] at hh
    rw [hh]
    fin_cases r <;> rfl
  · intro r hr
    exact Function.update_of_ne (hr 4).symm _ _

theorem on_queryFree {k : ℕ} (φ : Fin 13 ↪ Fin (k+1)) : (on φ).QueryFree :=
  rename_queryFree _ _ program_queryFree

end HiddenCircuits.Approximation.Initialization.WordMatrixLookup
