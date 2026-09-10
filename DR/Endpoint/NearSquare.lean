import DR.Endpoint.NearSquareParameters
import DR.Endpoint.BoundaryScaling

/-! Full closed-simplex endpoint theorem throughout the accepted near-square range. -/

namespace DittertRybin

/-- Rybin's endpoint on every m×n board with m≥117 and m≤n≤2m, and its transpose. -/
theorem uniform_maximum_short_endpoint {m n : ℕ} (hm : 117 ≤ m)
    (hmn : m ≤ n) (hn : n ≤ 2*m) :
    UniformMaximizer m n m ∧ UniformMaximizer n m m := by
  apply uniform_maximum_endpoint_of_arithmetic_criterion
    (g := 1) (by omega) (by omega) hmn (by decide) (one_dvd m) (one_dvd n)
  simpa only [Nat.cast_one, one_pow, mul_one] using endpoint_near_square_parameter_criterion hm hmn hn

end DittertRybin
