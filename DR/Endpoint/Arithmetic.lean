import DR.Endpoint.ArithmeticParameters
import DR.Endpoint.BoundaryScaling

/-! The accepted logarithmic aspect-ratio endpoint range, on the full closed
simplex and in both orientations. Natural logarithms and the real dimension
cutoff are explicit. -/

namespace DittertRybin

/-- Sharp endpoint uniqueness on the growing arithmetic range. -/
theorem uniform_maximum_arithmetic_endpoint {m n : ℕ}
    (hm : 128 ≤ m) (hmn : m ≤ n)
    (hcut : 22*(n : ℝ)*Real.log (m : ℝ) ≤ (m : ℝ)*(m-1)) :
    UniformMaximizer m n m ∧ UniformMaximizer n m m := by
  exact uniform_maximum_endpoint_of_boundary_criterion (by omega) (by omega) hmn
    (endpoint_arithmetic_scalar_criterion hm hmn hcut)

/-- The equivalent quotient form keeps the original stated upper endpoint. -/
theorem uniform_maximum_arithmetic_endpoint_of_le {m n : ℕ}
    (hm : 128 ≤ m) (hmn : m ≤ n)
    (hcut : (n : ℝ) ≤ (m : ℝ)*(m-1)/(22*Real.log (m : ℝ))) :
    UniformMaximizer m n m ∧ UniformMaximizer n m m := by
  have hlog := endpoint_arithmetic_log_gt_one hm
  have h := (le_div_iff₀ (by positivity : 0 < 22*Real.log (m : ℝ))).mp hcut
  apply uniform_maximum_arithmetic_endpoint hm hmn
  nlinarith only [h]

end DittertRybin
