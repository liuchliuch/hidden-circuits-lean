import HiddenCircuits.Complexity.OracleStream
import HiddenCircuits.Complexity.OracleMove

/-! A fixed finite list of actual unary copy operations
computes a linear expression. Repeated source ports are explicitly supported. -/
namespace HiddenCircuits.DH.Runtime.UnaryLinear
open Complexity Complexity.OracleBlock
variable {k : ℕ}
noncomputable def program (target temp : Fin (k+1)) (ports : List (Fin (k+1)))
    (h : ∀q∈ports,q≠target ∧ q≠temp) (ht : target≠temp) : OracleBlock k :=
  match ports with
  | []=>skip
  | q::qs=>seq (copyOn q target temp (h q (by simp)).1 (h q (by simp)).2 ht)
    (program target temp qs (fun q hq=>h q (List.mem_cons_of_mem _ hq)) ht)

theorem executes (g : BitString→ℕ) (target temp : Fin (k+1)) (ports : List (Fin (k+1)))
    (h : ∀q∈ports,q≠target ∧ q≠temp) (ht : target≠temp) (s : Store k)
    (values : Fin (k+1)→ℕ) (hv : ∀q∈ports,s q=List.replicate (values q) true)
    (hz : s temp=[]) (acc : ℕ) (ha : s target=List.replicate acc true) :
    (program target temp ports h ht).Executes g s
      (Function.update s target (List.replicate ((ports.map values).sum+acc) true))
      (5*(ports.map values).sum+4*ports.length+1) := by
  induction ports generalizing s acc with
  | nil=>simpa only [program,List.map_nil,List.sum_nil,List.length_nil,zero_mul,zero_add,
      ←ha,Function.update_eq_self] using skip_executes g s
  | cons q qs ih=>
    have hq:=h q List.mem_cons_self
    have hc:=copyOn_executes g q target temp hq.1 hq.2 ht s hz
    rw [hv q List.mem_cons_self,ha,←List.replicate_add,List.length_replicate] at hc
    have hh:∀p∈qs,p≠target ∧ p≠temp:=fun p hp=>h p (List.mem_cons_of_mem _ hp)
    have hv':∀p∈qs,Function.update s target (List.replicate (values q+acc) true) p=List.replicate (values p) true:=by
      intro p hp;rw [Function.update_of_ne (hh p hp).1];exact hv p (List.mem_cons_of_mem _ hp)
    have hz':Function.update s target (List.replicate (values q+acc) true) temp=[]:=by simp [ht.symm,hz]
    have hi:=ih hh _ hv' hz' (values q+acc) (by simp)
    convert seq_executes _ _ g hc hi using 1
    · simp [Function.update_idem,List.sum_cons,Nat.add_assoc,Nat.add_left_comm]
    · simp;ring
lemma queryFree (target temp : Fin (k+1)) (ports : List (Fin (k+1)))
    (h : ∀q∈ports,q≠target ∧ q≠temp) (ht : target≠temp) :
    (program target temp ports h ht).QueryFree := by
  induction ports with
  | nil=>exact skip_queryFree
  | cons q qs ih=>exact seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (ih _)
end HiddenCircuits.DH.Runtime.UnaryLinear
