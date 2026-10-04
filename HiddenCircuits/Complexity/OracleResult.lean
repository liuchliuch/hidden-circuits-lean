import HiddenCircuits.Complexity.OracleCleanup

/-! Relocate an arbitrary computed result to the conventional output stack and
clear every work stack by real bit instructions. -/
namespace HiddenCircuits.Complexity.OracleBlock
variable {k : ℕ}

noncomputable def cleanResult (out temp : Fin (k+1)) (hot : out ≠ temp)
    (htz : temp ≠ 0) : OracleBlock k :=
  seq (cleanup out) (seq (reverseOn out temp hot) (reverseOn temp 0 htz))

theorem cleanResult_executes (g : BitString → ℕ) (out temp : Fin (k+1))
    (hot : out ≠ temp) (htz : temp ≠ 0) (hoz : out ≠ 0)
    (s : Store k) (N : ℕ) (hs : ∀ i, (s i).length ≤ N) :
    ∃ cost, (cleanResult out temp hot htz).Executes g s
      (Function.update (fun _ => []) 0 (s out)) cost ∧
      cost ≤ (k+5)*(N+3)+1 := by
  obtain ⟨c,hc,hb⟩ := cleanup_executes g out s N hs
  let mid := Function.update (fun _ : Fin (k+1) => ([] : BitString)) temp (s out).reverse
  have h₁ : (reverseOn out temp hot).Executes g
      (Function.update (fun _ => []) out (s out)) mid (2*(s out).length+1) := by
    convert reverseOn_executes g out temp hot (Function.update (fun _ => []) out (s out)) using 1
    · funext i
      by_cases hi : i=out
      · subst i;simp [mid,hot,Ne.symm hot]
      · by_cases ht : i=temp
        · subst i;simp [mid,hot,Ne.symm hot]
        · simp [mid,hi,ht]
    · simp
  have h₂ : (reverseOn temp 0 htz).Executes g mid
      (Function.update (fun _ => []) 0 (s out)) (2*(s out).length+1) := by
    convert reverseOn_executes g temp 0 htz mid using 1
    · funext i
      by_cases hi : i=0
      · subst i;simp [mid,htz,Ne.symm htz]
      · by_cases ht : i=temp
        · subst i;simp [mid,htz]
        · simp [mid,hi,ht]
    · simp [mid]
  refine ⟨_,seq_executes _ _ g hc (seq_executes _ _ g h₁ h₂),?_⟩
  have ho := hs out
  nlinarith

lemma cleanResult_queryFree (out temp : Fin (k+1)) (hot : out ≠ temp) (htz : temp ≠ 0) :
    (cleanResult out temp hot htz).QueryFree :=
  seq_queryFree _ _ (cleanup_queryFree _) (seq_queryFree _ _
    (reverseOn_queryFree _ _ _) (reverseOn_queryFree _ _ _))

/-- A binary operation's initial layout; the two finite ports are explicit. -/
def binaryStore (x y : BitString) : Store (k+1) := fun i =>
  if i=0 then x else if i=1 then y else []

lemma binaryStore_bound (x y : BitString) :
    ∀ i, (binaryStore (k := k) x y i).length ≤ x.length+y.length := by
  intro i;simp only [binaryStore];split_ifs <;> simp <;> omega

noncomputable def cleanBinary (B : OracleBlock (k+1)) (out temp : Fin (k+2))
    (hot : out ≠ temp) (htz : temp ≠ 0) : OracleBlock (k+1) := seq B (cleanResult out temp hot htz)

/-- This lemma adds actual cleanup and relocation to an existing operational
binary routine; its cost comes from the proved execution storage bound. -/
theorem cleanBinary_executes (B : OracleBlock (k+1)) (out temp : Fin (k+2))
    (hot : out ≠ temp) (htz : temp ≠ 0) (hoz : out ≠ 0)
    (g : BitString → ℕ) (x y : BitString) (s : Store (k+1)) (z : BitString)
    (cost : ℕ) (h : B.Executes g (binaryStore x y) s cost) (ho : s out=z) :
    ∃ t, (cleanBinary B out temp hot htz).Executes g (binaryStore x y)
      (binaryStore z []) t ∧ t ≤ cost+(k+6)*(x.length+y.length+cost+3)+3 := by
  obtain ⟨c,hc,hb⟩ := cleanResult_executes g out temp hot htz hoz s
    (x.length+y.length+cost) (h.stack_bound (binaryStore_bound x y))
  refine ⟨cost+c+2,?_,?_⟩
  swap
  · have he : k+1+5=k+6 := by omega
    rw [he] at hb
    omega
  have hh := seq_executes _ _ g h hc
  convert hh using 1
  funext i
  by_cases hi : i=0
  · subst i;simp [binaryStore,ho]
  · simp [binaryStore,hi,ho]

end HiddenCircuits.Complexity.OracleBlock
