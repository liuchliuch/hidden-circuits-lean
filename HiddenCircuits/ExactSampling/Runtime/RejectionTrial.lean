import HiddenCircuits.ExactSampling.OperationalRejection
import HiddenCircuits.Complexity.OracleMove

/-! A fixed seven-stack trial checker with read-only count and sample ports.
The unbounded driver can reuse exactly this block after every fresh coin block;
all copies, comparison, and work cleanup are charged as bit instructions. -/
namespace HiddenCircuits.ExactSampling.Runtime.RejectionTrial
open Complexity OracleBlock BinaryArithmetic
open Approximation Approximation.FiniteChains Rejection

 def state (bound sample flag copiedSample copiedBound temporary scratch : BitString) : Store 6 := fun i =>
  ![bound,sample,flag,copiedSample,copiedBound,temporary,scratch] i

 def subPorts : Fin 4 ↪ Fin 7 where
  toFun i := ![3,4,5,2] i
  inj' := by decide +kernel

 noncomputable def program : OracleBlock 6 :=
  seq (copyOn 1 3 6 (by decide) (by decide) (by decide))
    (seq (copyOn 0 4 6 (by decide) (by decide) (by decide))
      (seq (rename subBlock subPorts) (clear 3)))

 theorem executes (g : BitString→ℕ) (bound sample : BitString) :
    ∃t,program.Executes g (state bound sample [] [] [] [] [])
      (state bound sample [decide (value sample<value bound)] [] [] [] []) t ∧
      t≤30*(bound.length+sample.length+1) := by
  have h1 : (copyOn (1:Fin 7) 3 6 (by decide) (by decide) (by decide)).Executes g
      (state bound sample [] [] [] [] []) (state bound sample [] sample [] [] []) (5*sample.length+2) := by
    convert copyOn_executes g (1:Fin 7) 3 6 (by decide) (by decide) (by decide)
      (state bound sample [] [] [] [] []) rfl using 1
    funext i;fin_cases i <;> simp [state]
  have h2 : (copyOn (0:Fin 7) 4 6 (by decide) (by decide) (by decide)).Executes g
      (state bound sample [] sample [] [] []) (state bound sample [] sample bound [] []) (5*bound.length+2) := by
    convert copyOn_executes g (0:Fin 7) 4 6 (by decide) (by decide) (by decide)
      (state bound sample [] sample [] [] []) rfl using 1
    funext i;fin_cases i <;> simp [state]
  have hsub := subBlock_executes g sample bound
  have hflag : (subRaw sample bound false).2=decide (value sample<value bound) := by
    apply Bool.eq_iff_iff.mpr
    simpa using subRaw_borrow sample bound
  rw [hflag] at hsub
  have h3 : (rename subBlock subPorts).Executes g (state bound sample [] sample bound [] [])
      (state bound sample [decide (value sample<value bound)] (subtractBits sample bound) [] [] [])
      (subCost sample bound) := by
    apply rename_executes_to subBlock subPorts g hsub
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | exact (hi 2 rfl).elim | exact (hi 3 rfl).elim
  have h4 : (clear (3:Fin 7)).Executes g
      (state bound sample [decide (value sample<value bound)] (subtractBits sample bound) [] [] [])
      (state bound sample [decide (value sample<value bound)] [] [] [] []) ((subtractBits sample bound).length+1) := by
    convert clear_executes g (3:Fin 7) _ using 1
    funext i;fin_cases i <;> rfl
  have hs := hsub.stack_bound (n:=sample.length+bound.length) (by
    intro i
    change (subStore sample bound [] [] i).length≤sample.length+bound.length
    fin_cases i <;> simp [subStore] <;> omega)
  have hh : (subtractBits sample bound).length≤sample.length+bound.length+subCost sample bound := hs (0:Fin 4)
  have ht := subCost_bound sample bound
  have hm : max sample.length bound.length≤sample.length+bound.length := by omega
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)),?_⟩
  omega

 theorem queryFree : program.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
   (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
     (seq_queryFree _ _ (rename_queryFree _ _ subBlock_queryFree) (clear_queryFree _)))

 theorem trial_executes (g : BitString→ℕ) (n : ℕ) (r : CoinTape (width n)) :
    ∃t,program.Executes g (state (Computability.encodeNat n) (List.ofFn r) [] [] [] [] [])
      (state (Computability.encodeNat n) (List.ofFn r) [decide ((attempt n r).isSome)] [] [] [] []) t ∧
      t≤60*(Nat.size n+1) := by
  obtain ⟨t,ht,hb⟩ := executes g (Computability.encodeNat n) (List.ofFn r)
  have he : decide (value (List.ofFn r)<value (Computability.encodeNat n))=
      decide ((attempt n r).isSome) := by
    rw [value_ofFn,value_encodeNat]
    by_cases ha : (tapeNumber (width n) r).val<n <;> simp [attempt,ha]
  rw [he] at ht
  refine ⟨t,ht,?_⟩
  simp only [encodeNat_length,List.length_ofFn] at hb
  have hw := width_le_size n
  omega

 noncomputable def retry : OracleBlock 6 := seq (clear 1) (clear 2)

 theorem retry_executes (g : BitString→ℕ) (n : ℕ) (r : CoinTape (width n)) :
    retry.Executes g (state (Computability.encodeNat n) (List.ofFn r) [false] [] [] [] [])
      (state (Computability.encodeNat n) [] [] [] [] [] []) (width n+5) := by
  have h1 : (clear (1:Fin 7)).Executes g
      (state (Computability.encodeNat n) (List.ofFn r) [false] [] [] [] [])
      (state (Computability.encodeNat n) [] [false] [] [] [] []) (width n+1) := by
    convert clear_executes g (1:Fin 7) _ using 1
    · funext i;fin_cases i <;> rfl
    · simp [state]
  have h2 : (clear (2:Fin 7)).Executes g
      (state (Computability.encodeNat n) [] [false] [] [] [] [])
      (state (Computability.encodeNat n) [] [] [] [] [] []) 2 := by
    convert clear_executes g (2:Fin 7) _ using 1
    funext i;fin_cases i <;> rfl
  convert seq_executes _ _ g h1 h2 using 1 <;> omega

/-- A single fixed trial block implements the finite proposal used by the
unbounded first-hit semantics. Retry clears every previous random/work bit. -/
 theorem retry_closed (g : BitString→ℕ) (n : ℕ) (r : Rejected n) :
    ∃t,(seq program retry).Executes g
      (state (Computability.encodeNat n) (List.ofFn r.val) [] [] [] [] [])
      (state (Computability.encodeNat n) [] [] [] [] [] []) t ∧ t≤70*(Nat.size n+1) := by
  obtain ⟨t,ht,hb⟩ := trial_executes g n r.val
  rw [r.property] at ht
  simp only [Option.isSome_none,decide_false] at ht
  refine ⟨_,seq_executes _ _ g ht (retry_executes g n r.val),?_⟩
  have hw := width_le_size n
  omega

end HiddenCircuits.ExactSampling.Runtime.RejectionTrial
