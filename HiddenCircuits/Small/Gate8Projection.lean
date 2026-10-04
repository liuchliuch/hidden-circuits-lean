import HiddenCircuits.Small.Gate8Powers
import HiddenCircuits.Small.Gate8Suffix0

namespace HiddenCircuits.Small
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_sweep_scale_rows :
    (fun a => (Gate8Suffix0Rows a).map (fun x => (x.1,(1/4096 : ℚ)*x.2))) =
      Gate8SweepRows := by
  decide +kernel

theorem gate8_sweep_scale : (1/4096 : ℚ) • Gate8Suffix0 = Gate8Sweep := by
  ext i j
  change (1/4096 : ℚ) * sparseRow (Gate8Suffix0Rows i) j = sparseRow (Gate8SweepRows i) j
  rw [← gate8_sweep_scale_rows]
  exact (sparseRow_scale (Gate8Suffix0Rows i) (1/4096) j).symm

end HiddenCircuits.Small
