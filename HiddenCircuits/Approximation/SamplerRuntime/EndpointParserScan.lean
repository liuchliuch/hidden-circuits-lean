import HiddenCircuits.Approximation.SamplerRuntime.EndpointParserRow

/-! Fresh reconstruction of the counted endpoint scan. Every raw input takes
one real row block per header bit; invariant bounds do not assume validity. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.EndpointParser.Scan
open Complexity OracleBlock

def run : ℕ → State → State
  | 0,s => s
  | n+1,s => run n (step s)
noncomputable def loop : OracleBlock 23 := whilePop 11 row row

lemma run_bounded (n N : ℕ) (s : State) (h : Bounded N s) : Bounded N (run n s) := by
  induction n generalizing s with
  | zero => exact h
  | succ n ih => exact ih _ (step_bounded N s h)
@[simp] lemma run_header (n : ℕ) (s : State) : (run n s).header=s.header := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact ih (step s)

theorem loop_executes (g : BitString → ℕ) (s : State) (clock : BitString) (N : ℕ) (h : Bounded N s) :
    ∃c, loop.Executes g (store s clock) (store (run clock.length s) []) c ∧
      c≤clock.length*(2000*(N+1)+2)+1 := by
  suffices hh : ∃c, WhileExecution (11:Fin 24) row row g (store s clock)
      (store (run clock.length s) []) c ∧ c≤clock.length*(2000*(N+1)+2)+1 by
    obtain ⟨c,hc,hb⟩ := hh
    exact ⟨c,whilePop_executes _ _ _ g hc,hb⟩
  induction clock generalizing s with
  | nil => exact ⟨1,WhileExecution.empty _ rfl,by simp⟩
  | cons b clock ih =>
    obtain ⟨a,ha,hab⟩ := row_executes g s clock N h
    obtain ⟨c,hc,hcb⟩ := ih (step s) (step_bounded N s h)
    have he : Function.update (store s (b::clock)) (11:Fin 24) clock=store s clock := by
      funext i; fin_cases i <;> rfl
    refine ⟨1+a+1+c,?_,?_⟩
    · cases b with
      | false => exact WhileExecution.zero rfl (by rw [he]; exact ha) hc
      | true => exact WhileExecution.one rfl (by rw [he]; exact ha) hc
    · simp only [List.length_cons]; nlinarith
lemma loop_queryFree : loop.QueryFree := whilePop_queryFree _ _ _ row_queryFree row_queryFree
end HiddenCircuits.Approximation.SamplerRuntime.EndpointParser.Scan
