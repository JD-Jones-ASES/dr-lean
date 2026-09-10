import DR.Endpoint.NearEndpointCutFloors
import DR.Endpoint.NearEndpointTransportParameters

namespace DittertRybin.Tests
open scoped BigOperators

-- The one-grid-step mixed cut is the largest-sensitive regime, not an axis cut.
example : nearEndpointSizedCutCoefficient 21 11 11 = 440 ∧
    nearEndpointSizedCutCoefficient 21 21 1 = 40 := by
  norm_num [nearEndpointSizedCutCoefficient]

-- Whole sets have zero discrepancy and coefficient, although their demand is positive.
example : nearEndpointSizedCutCoefficient 21 21 21 = 0 := by
  norm_num [nearEndpointSizedCutCoefficient]

-- A zero-demand cut has formal coefficient0; it cannot satisfy the positive-cut guard.
example : nearEndpointSizedCutCoefficient 21 10 11 = 0 ∧
    ¬(0 : ℝ) < (10 : ℝ)/21+11/21-1 := by
  norm_num [nearEndpointSizedCutCoefficient]

-- Padding shifts both surviving marginal dimensions and residual dimension by one.
example : nearEndpointRectangleFloor 3 2 2 = 8/81 ∧
    nearEndpointRectangleFloor 4 3 3 = 81/2048 := by
  norm_num [nearEndpointRectangleFloor,dittertConstant]

-- The weak guards include all five finite cases before the scalar n≥26 tail.
example : distinctUniformProbability 21 20 ≤ 1/4 ∧
    (4/3 : ℝ)*(21 : ℝ)^2*distinctUniformProbability 21 20 < 1 :=
  nearEndpoint_transport_parameter_bounds (by decide)

example : distinctUniformProbability 25 24 ≤ 1/4 ∧
    (4/3 : ℝ)*(25 : ℝ)^2*distinctUniformProbability 25 24 < 1 :=
  nearEndpoint_transport_parameter_bounds (by decide)

-- At zero rook deficit, every positive active cut forces q=1, without division by δ.
example {n : ℕ} (hn : 3 ≤ n) {P : Board n n} (hP : IsProbability P)
    (hc : uniformSeparationValue n n (n-1) ≤ separationProbability P (n-1))
    (hd : nearEndpointRookDeficit P=0) {q : ℝ} (hq : q≤1)
    (I J : Finset (Fin n)) (hp : 0<rectangularCutDemand I J)
    (ha : cutMass P I J=q*rectangularCutDemand I J) : q=1 := by
  have h := nearEndpoint_active_dilation_loss_sq hn hP hc hq I J hp ha
  rw [hd,mul_zero,zero_div] at h
  nlinarith [sq_nonneg (1-q)]

-- Both active-cut zeros and the actual padded permanent are required by this transfer.
example {n : ℕ} (hn : 2≤n) {B : Board n n} (hB : IsProbability B)
    (hr : ∀i,rowSum B i=1/(n:ℝ)) (hc : ∀j,colSum B j=1/(n:ℝ))
    (I J : Finset (Fin n)) (hp : 0<rectangularCutDemand I J)
    (hz : cutMass B Iᶜ Jᶜ=0) {v : ℝ} (hv : v≤(nearEndpointPadding B).permanent) :
    nearEndpointCutRookFloor n v I.card J.card≤nearEndpointRookRatio B :=
  nearEndpointRookRatio_sized_lower_bound hn hB hr hc I J hp hz hv

#print axioms nearEndpoint_marginal_variance_le
#print axioms nearEndpoint_contender_sized_subset_discrepancy_sq
#print axioms nearEndpoint_active_dilation_loss_sq
#print axioms nearEndpoint_contender_exists_active_dilation
#print axioms nearEndpointRookRatio_lower_of_padding
#print axioms nearEndpointPadding_complement_rectangle_lower
#print axioms nearEndpointRookRatio_sized_lower_bound
#print axioms nearEndpoint_transport_parameter_bounds
end DittertRybin.Tests
