import DR.Endpoint.NearEndpointParameters
import Mathlib.Tactic.IntervalCases

/-! The weak transport guards already hold throughout n≥21; only the
stronger final boundary comparison needs a finite cut-sensitive route. -/
namespace DittertRybin

set_option maxRecDepth 4096 in
theorem nearEndpoint_transport_parameter_bounds {n : ℕ} (hn : 21 ≤ n) :
    distinctUniformProbability n (n-1) ≤ 1/4 ∧
      (4/3 : ℝ)*(n : ℝ)^2*distinctUniformProbability n (n-1) < 1 := by
  by_cases h26 : 26 ≤ n
  · exact ⟨(nearEndpoint_parameter_bounds h26).1.le,(nearEndpoint_parameter_bounds h26).2.1⟩
  · have hn25 : n ≤ 25 := by omega
    interval_cases n <;> norm_num [distinctUniformProbability,Nat.descFactorial]

end DittertRybin
