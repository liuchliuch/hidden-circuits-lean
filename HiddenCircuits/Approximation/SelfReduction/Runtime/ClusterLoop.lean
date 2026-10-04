import HiddenCircuits.Approximation.SelfReduction.Runtime.ClusterBody
import HiddenCircuits.Approximation.SelfReduction.Runtime.UnaryValues
import HiddenCircuits.Approximation.SelfReduction.NaturalSelection

/-! The actual inner while
loop computes the finite neighborhood statistic from the encoded data. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

def neighborhoodCount (target radius : ℕ) (xs : List ℕ) : ℕ :=
  xs.countP (fun item => decide (item ≤ target+radius ∧ target ≤ item+radius))

noncomputable def neighborhoodScan : OracleBlock 12 := whilePop 3 skip clusterBody

theorem neighborhoodCount_le (target radius : ℕ) (xs : List ℕ) : neighborhoodCount target radius xs  ≤  xs.length :=
  List.countP_le_length

theorem neighborhoodScan_execution (g : BitString → ℕ) (target radius : ℕ) (xs : List ℕ)
    (count B : ℕ) (hxs : ∀ x ∈ xs, x ≤ B) :
    ∃ t, WhileExecution (3 : Fin 13) skip clusterBody g
      (clusterStore target radius count 0 (unaryValues xs) [] [])
      (clusterStore target radius (count+neighborhoodCount target radius xs) 0 [] [] []) t ∧
      t  ≤  1+xs.length*(80*(B+target+radius+1)) := by
  induction xs generalizing count with
  | nil =>
    refine ⟨1,?_,by simp⟩
    simpa [neighborhoodCount,unaryValues,encodeBitList] using
      (WhileExecution.empty (clusterStore target radius count 0 [] [] []) (by rfl))
  | cons x xs ih =>
    obtain ⟨tb,hb,hbt⟩ := clusterBody_executes g target radius count x (unaryValues xs)
    obtain ⟨tt,ht,htt⟩ := ih (count+if x ≤ target+radius ∧ target ≤ x+radius then 1 else 0)
      (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
    have hpop : Function.update (clusterStore target radius count 0 (unaryValues (x::xs)) [] [])
        (3 : Fin 13) (pairBits (List.replicate x true) (unaryValues xs)) =
        clusterStore target radius count 0 (pairBits (List.replicate x true) (unaryValues xs)) [] [] := by
      funext i; fin_cases i <;> rfl
    have hw := WhileExecution.one
      (s := clusterStore target radius count 0 (unaryValues (x::xs)) [] [])
      (rest := pairBits (List.replicate x true) (unaryValues xs)) (by rfl) (by rw [hpop]; exact hb) ht
    refine ⟨2+tb+tt,?_,?_⟩
    · convert hw using 1
      · congr 1
        by_cases hh : x ≤ target+radius ∧ target ≤ x+radius <;>
          simp [neighborhoodCount,List.countP_cons,hh,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      · omega
    · have hx := hxs x (List.mem_cons_self)
      simp only [List.length_cons]
      nlinarith

theorem neighborhoodScan_executes (g : BitString → ℕ) (target radius : ℕ) (xs : List ℕ)
    (count B : ℕ) (hxs : ∀ x ∈ xs, x ≤ B) :
    ∃ t, neighborhoodScan.Executes g
      (clusterStore target radius count 0 (unaryValues xs) [] [])
      (clusterStore target radius (count+neighborhoodCount target radius xs) 0 [] [] []) t ∧
      t  ≤  1+xs.length*(80*(B+target+radius+1)) := by
  obtain ⟨t,ht,hb⟩ := neighborhoodScan_execution g target radius xs count B hxs
  exact ⟨t,whilePop_executes _ _ _ _ ht,hb⟩

theorem neighborhoodCount_ofFn (n : ℕ) (q : Fin (n+1) → ℕ) (radius : ℕ) (i : Fin (n+1)) :
    neighborhoodCount (q i) radius (List.ofFn q) = (naturalCluster n q radius i).card := by
  have hs (xs : List ℕ) : xs.countP (fun x => decide (x ≤ q i+radius ∧ q i ≤ x+radius)) =
      (xs.map (fun x => if x ≤ q i+radius ∧ q i ≤ x+radius then 1 else 0)).sum := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.countP_cons,List.map_cons,List.sum_cons,ih]
      by_cases h : x ≤ q i+radius ∧ q i ≤ x+radius <;> simp [h] <;> omega
  unfold neighborhoodCount naturalCluster
  rw [hs,List.map_ofFn,List.sum_ofFn,Finset.card_filter]
  rfl

end HiddenCircuits.Approximation.SelfReduction.Runtime
