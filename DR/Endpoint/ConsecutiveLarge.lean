import DR.Endpoint.ConsecutiveParameters
import DR.Endpoint.BoundaryScaling

/-! The unrestricted probability-simplex consecutive endpoint for every m≥30.
The separate finite cases needed for the accepted m≥19 range are not asserted here. -/

namespace DittertRybin

theorem uniform_maximum_consecutive_endpoint_of_thirty_le {m : ℕ} (hm : 30 ≤ m) :
    UniformMaximizer m (m+1) m ∧ UniformMaximizer (m+1) m m :=
  uniform_maximum_endpoint_of_boundary_criterion (by omega) (by omega) (by omega)
    (endpoint_consecutive_parameter_criterion hm)

end DittertRybin
