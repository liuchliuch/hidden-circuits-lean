import HiddenCircuits.ExactSampling.Runtime.WeightedSelect
import HiddenCircuits.ExactSampling.DHWeights

/-! Correspondence of the physical binary interval scanner with the exact
count-weighted matching branch bijection. -/
namespace HiddenCircuits.ExactSampling.Runtime.WeightedSelect
open Complexity OracleBlock DH Approximation Approximation.SelfReduction DHWeights
open scoped BigOperators

 theorem select_sigma {n : ℕ} (w : Fin n→ℕ) (j : Fin n) (r : Fin (w j)) :
    select (List.ofFn w) (finSigmaFinEquiv ⟨j,r⟩).val=(j.val,r.val,true) := by
  let j' : Fin (List.ofFn w).length := ⟨j.val,by simpa using j.isLt⟩
  have hr : r.val<(List.ofFn w)[j'.val] := by simpa [j'] using r.isLt
  have hh := select_interval (List.ofFn w) j' r.val hr
  have hp : ((List.ofFn w).take j.val).sum=∑i : Fin j.val,w (Fin.castLE j.isLt.le i) := by
    rw [←Fin.ofFn_take_eq_take_ofFn j.isLt.le w,List.sum_ofFn]
    rfl
  simpa only [j',hp,finSigmaFinEquiv_apply] using hh

 theorem select_splitIndex {N : ℕ} (G : MatrixGraph (N+1))
    (hG : DistanceHereditaryGraph G.graph) (x : Fin (count ⟨N+1,G⟩)) :
    select (List.ofFn (weight G)) x.val=
      ((splitIndex G hG x).1.val,(splitIndex G hG x).2.val,true) := by
  have h := select_sigma (weight G) (splitIndex G hG x).1 (splitIndex G hG x).2
  have he : finSigmaFinEquiv (splitIndex G hG x)=finCongr (count_eq_sum_weights G hG) x := by
    simp [splitIndex]
  rw [he] at h
  exact h

 theorem program_exact_choice (g : BitString→ℕ) {N : ℕ} (G : MatrixGraph (N+1))
    (hG : DistanceHereditaryGraph G.graph) (x : Fin (count ⟨N+1,G⟩)) :
    ∃t,program.Executes g (store (List.ofFn (weight G)) x.val 0)
      (result (splitIndex G hG x).2.val (splitIndex G hG x).1.val true) t ∧
      t≤(N+2)*(60*((encodeBitList ((List.ofFn (weight G)).map Computability.encodeNat)).length+
        Nat.size x.val+1)+60) := by
  simpa only [select_splitIndex G hG x,List.length_ofFn,Nat.zero_add,Nat.add_assoc] using
    program_executes g (List.ofFn (weight G)) x.val 0

 noncomputable def programOn {k : ℕ} (φ : Fin 11↪Fin (k+1)) : OracleBlock k := rename program φ

 theorem programOn_executes {k : ℕ} (φ : Fin 11↪Fin (k+1)) (g : BitString→ℕ)
    (s t : Store k) (ws : List ℕ) (r j : ℕ)
    (hs : s∘φ=store ws r j)
    (ht : t∘φ=result (select ws r).2.1 (j+(select ws r).1) (select ws r).2.2)
    (hf : ∀i,(∀a,φ a≠i)→t i=s i) :
    ∃c,(programOn φ).Executes g s t c ∧
      c≤(ws.length+1)*(60*((encodeBitList (ws.map Computability.encodeNat)).length+Nat.size r+1)+60) := by
  obtain ⟨c,hc,hb⟩ := program_executes g ws r j
  exact ⟨c,rename_executes_to program φ g hc hs ht hf,hb⟩

 theorem programOn_queryFree {k : ℕ} (φ : Fin 11↪Fin (k+1)) : (programOn φ).QueryFree :=
  rename_queryFree _ _ program_queryFree

end HiddenCircuits.ExactSampling.Runtime.WeightedSelect
