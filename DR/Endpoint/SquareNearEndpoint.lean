import DR.Endpoint.NearEndpointConditional
import DR.Endpoint.TwoZeroPermanent

/-! The complete square near-endpoint theorem. The actual two-independent-zero
permanent floor discharges the final transport input on every boundary support.
All finite dimensions 21 through 25 and every dimension at least26 are covered. -/
namespace DittertRybin

theorem nearEndpoint_required_permanent_bound {n : ℕ} (hn : 21 ≤ n) :
    TwoIndependentZeroPermanentBound (n+1) (nearEndpointRequiredPermanentFloor n) := by
  intro D hD hz
  by_cases h : n ≤ 25
  · obtain ⟨i₁,i₂,j₁,j₂,hi,hj,hz₁,hz₂⟩ := hz
    have hgap := permanent_two_zero_finite_gap hn h hD i₁ i₂ j₁ j₂ hi hj hz₁ hz₂
    simpa [nearEndpointRequiredPermanentFloor,h] using hgap.le
  · have hgap := permanent_two_independent_zero_gap (by omega : 27 ≤ n+1) hD hz
    have he : ((n : ℝ)+1)-2=(n : ℝ)-1 := by ring
    simpa [nearEndpointRequiredPermanentFloor,h,Nat.cast_add,he] using hgap.le

/-- On every n by n probability board with n at least21, uniform uniquely
maximizes separation of n-1 iid cells. The entire closed simplex is included. -/
theorem uniform_maximum_square_near_endpoint {n : ℕ} (hn : 21 ≤ n) :
    UniformMaximizer n n (n-1) :=
  nearEndpoint_uniformMaximizer_of_permanent_bound hn (nearEndpoint_required_permanent_bound hn)

end DittertRybin
