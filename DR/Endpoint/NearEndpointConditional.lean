import DR.Endpoint.NearEndpointBoundaryFinite
import DR.Endpoint.PositiveMaximizers
import DR.Endpoint.NearEndpointTwoZeroPolynomial
import DR.Endpoint.TwoZeroLogTail

/-! Conditional completion of the near-endpoint transport argument. The only
unproved input in this module is an explicit permanent inequality on actual
doubly stochastic matrices with two independent zeros. -/
namespace DittertRybin
open Certificates

/-- The exact finite reference is used through 25, then the analytic tail. -/
noncomputable def nearEndpointRequiredPermanentFloor (n : ℕ) : ℝ :=
  if n ≤ 25 then (nearEndpointPermanentFloorRat n : ℝ)
  else boundaryPermanentFloor (n+1)*(1+1/(4*((n : ℝ)-1)^2))

theorem nearEndpoint_boundary_contender_impossible_of_permanent_bound {n : ℕ}
    (hn : 21 ≤ n)
    (hfloor : TwoIndependentZeroPermanentBound (n+1) (nearEndpointRequiredPermanentFloor n))
    {P : Board n n} (hP : IsProbability P)
    (hcont : uniformSeparationValue n n (n-1) ≤ separationProbability P (n-1))
    (hz : ∃ i j, P i j=0) : False := by
  by_cases h : n ≤ 25
  · exact nearEndpoint_boundary_contender_impossible_finite hn h
      (by simpa [nearEndpointRequiredPermanentFloor,h] using hfloor) hP hcont hz
  · exact nearEndpoint_boundary_contender_impossible_tail (by omega)
      (by simpa [nearEndpointRequiredPermanentFloor,h] using hfloor) hP hcont hz

theorem nearEndpoint_uniformMaximizer_of_permanent_bound {n : ℕ} (hn : 21 ≤ n)
    (hfloor : TwoIndependentZeroPermanentBound (n+1) (nearEndpointRequiredPermanentFloor n)) :
    UniformMaximizer n n (n-1) := by
  apply uniform_maximizer_of_all_global_positive (by omega) (by omega) (by omega)
  intro P hP hmax i j
  by_contra h
  have hz : P i j=0 := le_antisymm (le_of_not_gt h) (hP.1 i j)
  have hcont := hmax (uniformBoard n n) (uniformBoard_isProbability (by omega) (by omega))
  rw [separationProbability_uniform (by omega) (by omega)] at hcont
  exact nearEndpoint_boundary_contender_impossible_of_permanent_bound hn hfloor hP hcont ⟨i,j,hz⟩

/-- The scalar polynomial lies above the required permanent reference on the
entire closed parameter rectangle, in both the finite and infinite ranges. -/
theorem nearEndpointRequiredPermanentFloor_lt_reduced {n : ℕ} (hn : 21 ≤ n)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haM : a ≤ 1/((n-1 : ℕ) : ℝ)) (hbM : b ≤ 1/((n-1 : ℕ) : ℝ)) :
    nearEndpointRequiredPermanentFloor n < twoZeroReducedPermanent (n-1) a b := by
  by_cases h : n ≤ 25
  · simpa [nearEndpointRequiredPermanentFloor,h] using
      nearEndpoint_twoZeroReducedPermanent_finite_lt hn h ha hb haM hbM
  · have hgap := twoZeroReducedPermanent_tail_gap (by omega : 25 ≤ n-1) ha hb haM hbM
    have hdim : n-1+2=n+1 := by omega
    simpa [nearEndpointRequiredPermanentFloor,h,hdim,Nat.cast_sub (by omega : 1 ≤ n)] using hgap

/-- This adapter records the exact remaining matrix obligation without
postulating a minimizer or a desired semimatching conclusion. -/
theorem nearEndpoint_permanent_bound_of_reduced_form {n : ℕ} (hn : 21 ≤ n)
    (hreduce : ∀ D : Board (n+1) (n+1), D ∈ doublyStochastic ℝ (Fin (n+1)) →
      (∃ i₁ i₂ j₁ j₂, i₁ ≠ i₂ ∧ j₁ ≠ j₂ ∧ D i₁ j₁=0 ∧ D i₂ j₂=0) →
      ∃ a b : ℝ, 0 ≤ a ∧ a ≤ 1/((n-1 : ℕ) : ℝ) ∧
        0 ≤ b ∧ b ≤ 1/((n-1 : ℕ) : ℝ) ∧ twoZeroReducedPermanent (n-1) a b ≤ D.permanent) :
    TwoIndependentZeroPermanentBound (n+1) (nearEndpointRequiredPermanentFloor n) := by
  intro D hD hz
  obtain ⟨a,b,ha,haM,hb,hbM,hle⟩ := hreduce D hD hz
  exact (nearEndpointRequiredPermanentFloor_lt_reduced hn ha hb haM hbM).le.trans hle

end DittertRybin
