import DR.Endpoint.DoubleParameters
import DR.Endpoint.BoundaryScaling

/-! Full closed-simplex endpoint theorem on every doubled rectangle m×2m, m≥80. -/

namespace DittertRybin

/-- The arithmetic gain m gives the entire accepted doubled family, with unique uniform equality. -/
theorem uniform_maximum_double_endpoint {m : ℕ} (hm : 80 ≤ m) :
    UniformMaximizer m (2*m) m ∧ UniformMaximizer (2*m) m m := by
  apply uniform_maximum_endpoint_of_arithmetic_criterion
    (g := m) (by omega) (by omega) (by omega) (by omega) (dvd_refl m) (dvd_mul_left m 2)
  exact endpoint_double_parameter_criterion hm

end DittertRybin
