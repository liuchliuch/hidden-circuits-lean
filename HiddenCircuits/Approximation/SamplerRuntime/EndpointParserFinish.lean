import HiddenCircuits.Approximation.SamplerRuntime.EndpointParserScan
import HiddenCircuits.Approximation.SamplerRuntime.EndpointParserEmpty
import HiddenCircuits.Complexity.GraphVerifier.HeaderStage

/-! Fresh reconstruction of exact exhaustion checks and charged cleanup. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.EndpointParser.Scan
open Complexity OracleBlock GraphVerifier.Runtime
set_option maxHeartbeats 800000

def result (s : State) : Bool := s.valid && s.lows.isEmpty && s.highs.isEmpty
def finalStore (header : BitString) (v : Bool) : Store 23 := fun i =>
  if i.val=0 then header else if i.val=6 then [v] else []
def output (s : State) : Store 23 := finalStore s.header (result s)
def emptiedLow (s : State) : Store 23 := Function.update (Function.update (store s []) 3 []) 7 [s.lows.isEmpty]
def emptiedBoth (s : State) : Store 23 := Function.update (Function.update (emptiedLow s) 4 []) 8 [s.highs.isEmpty]
def finalInputs : List (Fin 24) := [5,7,8]
def finalBits (s : State) (i : Fin 24) : Bool := if i.val=5 then s.valid else if i.val=7 then s.lows.isEmpty else s.highs.isEmpty
def finalDecided (s : State) : Store 23 := Function.update (eraseStore finalInputs (emptiedBoth s)) 6 [result s]
noncomputable def finish : OracleBlock 23 := seq (emptyCheck 3 7) (seq (emptyCheck 4 8)
  (seq (decision 6 finalInputs (fun bs => bs.all id)) (clearList [1,2])))
noncomputable def program : OracleBlock 23 := seq loop finish

theorem finish_executes (g : BitString → ℕ) (s : State) (N : ℕ) (h : Bounded N s) :
    ∃c,finish.Executes g (store s []) (output s) c ∧ c≤10*N+100 := by
  obtain ⟨a,ha,hab⟩ := emptyCheck_executes (3:Fin 24) 7 (by decide) g (store s []) rfl
  obtain ⟨b,hb,hbb⟩ := emptyCheck_executes (4:Fin 24) 8 (by decide) g (emptiedLow s) rfl
  have h₁ : (emptyCheck (3:Fin 24) 7).Executes g (store s []) (emptiedLow s) a := ha
  have h₂ : (emptyCheck (4:Fin 24) 8).Executes g (emptiedLow s) (emptiedBoth s) b := hb
  have h₃ : (decision (6:Fin 24) finalInputs (fun bs => bs.all id)).Executes g (emptiedBoth s) (finalDecided s) 10 := by
    have hh := decision_executes (6:Fin 24) finalInputs (by decide) (by decide)
      (fun bs => bs.all id) (finalBits s) g (emptiedBoth s) (by
        intro i hi; simp only [finalInputs,List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl|rfl <;> rfl)
    have he : (finalInputs.map (finalBits s)).all id=result s := by simp [finalInputs,finalBits,result,Bool.and_assoc]
    simpa only [he] using hh
  have hh : ∀i,(finalDecided s i).length≤N+1 := by
    intro i; fin_cases i <;>
      simp [finalDecided,eraseStore,finalInputs,emptiedBoth,emptiedLow,store]
    all_goals rcases h with ⟨h₀,h₁,h₂,h₃,h₄⟩; omega
  obtain ⟨c,hc,hcb⟩ := clearList_executes g [(1:Fin 24),2] (finalDecided s) (N+1) hh
  have h₄ : (clearList [(1:Fin 24),2]).Executes g (finalDecided s) (output s) c := by
    convert hc using 1
    funext i; fin_cases i <;> simp [output,finalStore,eraseStore,finalDecided,finalInputs,emptiedBoth,emptiedLow,store]
  refine ⟨_,seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ h₄)),?_⟩
  change a≤s.lows.length+6 at hab
  change b≤s.highs.length+6 at hbb
  simp only [List.length_cons,List.length_nil] at hcb
  rcases h with ⟨h₀,h₁,h₂,h₃,h₄⟩
  omega

theorem program_executes (g : BitString → ℕ) (s : State) (clock : BitString) (N : ℕ) (h : Bounded N s) :
    ∃c,program.Executes g (store s clock) (finalStore s.header (result (run clock.length s))) c ∧
      c≤clock.length*(2000*(N+1)+2)+10*N+103 := by
  obtain ⟨a,ha,hab⟩ := loop_executes g s clock N h
  obtain ⟨b,hb,hbb⟩ := finish_executes g (run clock.length s) N (run_bounded _ _ _ h)
  refine ⟨a+b+2,?_,by omega⟩
  simpa only [output,run_header] using seq_executes _ _ g ha hb
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ loop_queryFree
  (seq_queryFree _ _ (emptyCheck_queryFree _ _) (seq_queryFree _ _ (emptyCheck_queryFree _ _)
    (seq_queryFree _ _ (decision_queryFree _ _ _) (clearList_queryFree _))))
end HiddenCircuits.Approximation.SamplerRuntime.EndpointParser.Scan
