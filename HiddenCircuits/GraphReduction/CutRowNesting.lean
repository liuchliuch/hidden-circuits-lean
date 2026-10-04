import HiddenCircuits.PairedSampling
import HiddenCircuits.GraphReduction.LayeredChordal

/-! Actual row-neighborhood inclusion for every permitted cut, including perturbations. -/
namespace HiddenCircuits
namespace CutPair

theorem first_rows_nested {p : ℕ} (P : CutPair p) (a b v : Fin (2*p))
    (hab : a.val≤b.val) (hb : P.first b v=1) : P.first a v=1 := by
  cases P <;> simp only [first,addedCut,deletedCut,upper] at * <;>
    split_ifs at * <;> simp_all only [Fin.le_iff_val_le_val,zero_ne_one,one_ne_zero,and_true,true_and] <;> omega

theorem second_rows_nested {p : ℕ} (P : CutPair p) (a b v : Fin (2*p))
    (hab : a.val≤b.val) (ha : P.second a v=1) : P.second b v=1 := by
  cases P <;> simp only [second,Matrix.transpose_apply,addedCut,deletedCut,upper] at * <;>
    split_ifs at * <;> simp_all only [Fin.le_iff_val_le_val,zero_ne_one,one_ne_zero,and_true,true_and] <;> omega

end CutPair
end HiddenCircuits
