import DR.Endpoint.ColumnFailureComparison
import DR.Endpoint.UniformCollisionRemainder
import DR.Endpoint.LongColumnVariance

/-! The retained-uniform contender comparison for the actual endpoint
functional. The event union, column Schur bound and uniform remainder are
all proved separately; no gauge or row-concentration premise is assumed. -/
namespace DittertRybin
open scoped BigOperators

theorem endpoint_contender_leading_comparison {m n : ℕ} (hm : 3≤m) (hmn : m≤n)
    (P : Board m n) (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m≤separationProbability P m)
    (C : ℝ) (hC : ∀ j,colSum P j≤C) :
    (endpointLeadingGauge P)^2-(1-dittertConstant m)+
      (n:ℝ)*centeredVariance (endpointLeadingColumnCost P)≤
        (n:ℝ)*(((m-2:ℕ):ℝ)*(((m-2:ℕ):ℝ)+3)/2)*C*marginalVariance (colSum P)+
          dittertConstant m*(((m-2:ℕ):ℝ)*(((m-2:ℕ):ℝ)+3)/2)/(2*(n:ℝ)) := by
  have hm2 : 2≤m := by omega
  have hn : 0<n := by omega
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hA : (0:ℝ)<(m.choose 2:ℝ) := by exact_mod_cast Nat.choose_pos hm2
  have ha : 0≤dittertConstant m := (dittertConstant_pos (by omega : 0<m)).le
  let a := dittertConstant m
  let A : ℝ := (m.choose 2:ℝ)
  let b : ℝ := ((m-2:ℕ):ℝ)*(((m-2:ℕ):ℝ)+3)/2
  let q := 1-distinctUniformProbability n m
  let V := marginalVariance (colSum P)
  let W := centeredVariance (endpointLeadingColumnCost P)
  let G := endpointLeadingGauge P
  let E := ∑ j,((colSum P j)^2-(endpointLeadingColumnCost P j)^2)
  have hs : (∑ j,colSum P j)=1 := (totalMass_eq_sum_colSum P).symm.trans hP.2
  have hc := endpoint_column_failure_comparison hn hm2 (colSum P) (colSum_nonneg hP.1) hs C hC
  have he := endpoint_failure_leading_lower hm P hP
  have hcap : 1-separationProbability P m≤(1-a)*q := by
    rw [uniformSeparationValue_rectangular_endpoint] at hcont
    dsimp [a,q]
    nlinarith only [hcont]
  have hsum : E=V+1/(n:ℝ)-(W+G^2/(n:ℝ)) := by
    have hcv := marginalVariance_eq_sum_sq hn hs
    have hw := centeredVariance_eq_sum_sq hn (endpointLeadingColumnCost P)
    change W=(∑ j,(endpointLeadingColumnCost P j)^2)-G^2/(n:ℝ) at hw
    change V=(∑ j,(colSum P j)^2)-1/(n:ℝ) at hcv
    dsimp [E]
    rw [Finset.sum_sub_distrib]
    linarith only [hcv,hw]
  have hraw : q+A*(1-b*C)*V-A*E-(1-a)*q≤0 := by
    change (1-(m.factorial:ℝ)*elementarySymmetric (colSum P) m)-A*E≤1-separationProbability P m at he
    change (m.choose 2:ℝ)*(1-((m-2:ℕ):ℝ)*(((m-2:ℕ):ℝ)+3)*C/2)*V≤
      (1-(m.factorial:ℝ)*elementarySymmetric (colSum P) m)-q at hc
    dsimp [A,b]
    nlinarith only [hc,he,hcap]
  have hid : (A/(n:ℝ))*(G^2-(1-a)+(n:ℝ)*W-(n:ℝ)*b*C*V)-a*(A/(n:ℝ)-q)=
      q+A*(1-b*C)*V-A*E-(1-a)*q := by
    rw [hsum]
    field_simp
    ring
  have hmain : (A/(n:ℝ))*(G^2-(1-a)+(n:ℝ)*W-(n:ℝ)*b*C*V)≤a*(A/(n:ℝ)-q) := by
    rw [← hid] at hraw
    linarith only [hraw]
  have hrem := mul_le_mul_of_nonneg_left (endpoint_uniform_collision_remainder hm2 hn hmn).2 ha
  change a*(A/(n:ℝ)-q)≤a*(A*b/(2*(n:ℝ)^2)) at hrem
  have hprod := hmain.trans hrem
  have heq : a*(A*b/(2*(n:ℝ)^2))=(A/(n:ℝ))*(a*b/(2*(n:ℝ))) := by
    field_simp
  rw [heq] at hprod
  have hfinal := (mul_le_mul_iff_right₀ (div_pos hA hnR)).mp hprod
  change G^2-(1-a)+(n:ℝ)*W≤(n:ℝ)*b*C*V+a*b/(2*(n:ℝ))
  linarith only [hfinal]

end DittertRybin
