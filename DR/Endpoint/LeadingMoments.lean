import DR.Endpoint.LeadingStationarity

/-!
# Exact weighted moments of the leading gauge

These identities hold on the actual fixed nonidentical row law, including
empty columns. They provide the weighted Cauchy and common-multiplier
normalization needed by the penalized minimum argument.
-/
namespace DittertRybin
open scoped BigOperators
open Certificates
set_option backward.isDefEq.respectTransparency false

private theorem leading_cost_square {m n : ℕ} (hm : 3≤m)
    (r : Fin m → ℝ) (X : Board m n) (hr : ∀ i,0≤r i) (hs : ∑ i,r i=1)
    (hX : ∀ i j,0≤X i j) (hXS : ∀ i,rowSum X i=1) (j : Fin n) :
    (endpointLeadingColumnCost (endpointRowBoard r X) j)^2=
      (∑ i,r i*X i j)^2-endpointLeadingScale r*endpointLeadingColumnCollision X j := by
  have h := (endpointLeadingKernel_quadratic_bounds hm r (fun i => r i*X i j)
    hr hs (fun i => mul_nonneg (hr i) (hX i j))).1
  have hq : 0≤quadraticValue (endpointLeadingKernel r) (fun i => r i*X i j) :=
    (mul_nonneg (by linarith [(endpointLeadingDefect_bounds hm).2]) (sq_nonneg _)).trans h
  unfold endpointLeadingColumnCost
  rw [rowSum_endpointRowBoard r X hXS]
  change (Real.sqrt (quadraticValue (endpointLeadingKernel r) (fun i => r i*X i j)))^2=_
  rw [Real.sq_sqrt hq,endpointLeadingKernel_scaled_quadratic]
  unfold endpointLeadingColumnCollision
  ring

theorem endpointLeading_cost_mul_ratio {m n : ℕ} (hm : 3≤m)
    (r : Fin m → ℝ) (X : Board m n) (hr : ∀ i,0≤r i) (hs : ∑ i,r i=1)
    (hX : ∀ i j,0≤X i j) (hXS : ∀ i,rowSum X i=1) (j : Fin n) :
    endpointLeadingColumnCost (endpointRowBoard r X) j*endpointLeadingRatio r X j=
      ∑ i,r i*X i j := by
  by_cases hh : endpointLeadingColumnCost (endpointRowBoard r X) j=0
  · have hc := (endpointLeadingColumnCost_eq_zero_iff hm (endpointRowBoard r X)
      (endpointRowBoard_isProbability r X hr hs hX hXS) j).mp hh
    change (∑ i,r i*X i j)=0 at hc
    simp only [hh,zero_mul,hc]
  · unfold endpointLeadingRatio
    exact mul_div_cancel₀ _ hh

theorem endpointLeading_column_moment {m n : ℕ} (hm : 3≤m)
    (r : Fin m → ℝ) (X : Board m n) (hr : ∀ i,0≤r i) (hs : ∑ i,r i=1)
    (hX : ∀ i j,0≤X i j) (hXS : ∀ i,rowSum X i=1) (j : Fin n) :
    (∑ i,r i*X i j)*endpointLeadingRatio r X j=
      endpointLeadingColumnCost (endpointRowBoard r X) j+
      endpointLeadingScale r*(endpointLeadingColumnCollision X j/
        endpointLeadingColumnCost (endpointRowBoard r X) j) := by
  by_cases hh : endpointLeadingColumnCost (endpointRowBoard r X) j=0
  · simp [endpointLeadingRatio,hh]
  · have hsq := leading_cost_square hm r X hr hs hX hXS j
    unfold endpointLeadingRatio
    field_simp [hh]
    nlinarith only [hsq]

/-- The first weighted moment is exactly one, including empty columns. -/
theorem endpointLeading_weighted_sum_one {m n : ℕ} (hm : 3≤m)
    (r : Fin m → ℝ) (X : Board m n) (hr : ∀ i,0≤r i) (hs : ∑ i,r i=1)
    (hX : ∀ i j,0≤X i j) (hXS : ∀ i,rowSum X i=1) :
    (∑ j,endpointLeadingColumnCost (endpointRowBoard r X) j*endpointLeadingRatio r X j)=1 := by
  simp_rw [endpointLeading_cost_mul_ratio hm r X hr hs hX hXS]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum,show ∀ i,∑ j,X i j=1 from hXS,mul_one,hs]

/-- Exact second weighted moment, not a collision or independence approximation. -/
theorem endpointLeading_weighted_sum_two {m n : ℕ} (hm : 3≤m)
    (r : Fin m → ℝ) (X : Board m n) (hr : ∀ i,0≤r i) (hs : ∑ i,r i=1)
    (hX : ∀ i j,0≤X i j) (hXS : ∀ i,rowSum X i=1) :
    (∑ j,endpointLeadingColumnCost (endpointRowBoard r X) j*(endpointLeadingRatio r X j)^2)=
      endpointLeadingGauge (endpointRowBoard r X)+2*endpointLeadingMoment r X := by
  have he (j : Fin n) : endpointLeadingColumnCost (endpointRowBoard r X) j*(endpointLeadingRatio r X j)^2=
      endpointLeadingColumnCost (endpointRowBoard r X) j+
      endpointLeadingScale r*(endpointLeadingColumnCollision X j/
        endpointLeadingColumnCost (endpointRowBoard r X) j) := by
    rw [pow_two,← mul_assoc,endpointLeading_cost_mul_ratio hm r X hr hs hX hXS]
    exact endpointLeading_column_moment hm r X hr hs hX hXS j
  simp only [he,Finset.sum_add_distrib,← Finset.mul_sum,endpointLeadingGauge,endpointLeadingMoment]
  ring

/-- Actual weighted Cauchy--Schwarz. Its left side is one because the row
law and row masses are normalized; no positivity of a minimizer is assumed. -/
theorem endpointLeading_weighted_cauchy {m n : ℕ} (hm : 3≤m)
    (r : Fin m → ℝ) (X : Board m n) (hr : ∀ i,0≤r i) (hs : ∑ i,r i=1)
    (hX : ∀ i j,0≤X i j) (hXS : ∀ i,rowSum X i=1) :
    1≤endpointLeadingGauge (endpointRowBoard r X)*
      (endpointLeadingGauge (endpointRowBoard r X)+2*endpointLeadingMoment r X) := by
  let H : Fin n → ℝ := endpointLeadingColumnCost (endpointRowBoard r X)
  let Z := endpointLeadingRatio r X
  have hh (j : Fin n) : 0≤H j := Real.sqrt_nonneg _
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r:=fun j => H j*Z j) (f:=H) (g:=fun j => H j*(Z j)^2)
    (fun j _ => hh j) (fun j _ => mul_nonneg (hh j) (sq_nonneg _))
    (fun j _ => by nlinarith)
  dsimp only [H,Z] at h
  rw [endpointLeading_weighted_sum_one hm r X hr hs hX hXS,
    endpointLeading_weighted_sum_two hm r X hr hs hX hXS,one_pow] at h
  exact h

/-- Weighted normalization of the row derivative. -/
theorem endpointLeading_rowDerivative_sum {m n : ℕ} (hm : 3≤m)
    (r : Fin m → ℝ) (X : Board m n) (hr : ∀ i,0≤r i) (hs : ∑ i,r i=1)
    (hX : ∀ i j,0≤X i j) (hXS : ∀ i,rowSum X i=1) :
    (∑ i,r i*endpointLeadingRowDerivative r X i)=
      endpointLeadingGauge (endpointRowBoard r X)+2*endpointLeadingMoment r X := by
  have he : (∑ i,r i*endpointLeadingRowDerivative r X i)=
      ∑ j,(∑ i,r i*X i j)*endpointLeadingRatio r X j := by
    simp only [endpointLeadingRowDerivative,Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he]
  simp_rw [endpointLeading_column_moment hm r X hr hs hX hXS]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,endpointLeadingGauge,endpointLeadingMoment]
  ring

/-- The advertised stationary row identity is derived from the true
minimum, pair directions and the exact weighted moment normalization. -/
theorem IsEndpointRowGaugeMinimum.stationarity {m n : ℕ} (hm : 3≤m)
    {r : Fin m → ℝ} {X : Board m n} {psi : ℝ → ℝ}
    (hmin : IsEndpointRowGaugeMinimum r X psi) (hr : ∀ i,0<r i) (hs : ∑ i,r i=1)
    (hX : ∀ i j,0≤X i j) (hXS : ∀ i,rowSum X i=1) (tau : ℝ)
    (hpsi : HasDerivAt psi tau (∑ i,r i^2)) (i : Fin m) :
    endpointLeadingRowDerivative r X i=
      endpointLeadingGauge (endpointRowBoard r X)-((m:ℝ)-2)*endpointLeadingMoment r X+
      2*tau*(r i-(∑ a,r a^2))+endpointLeadingMoment r X/r i := by
  let F : Fin m → ℝ := fun a =>
    endpointLeadingRowDerivative r X a-endpointLeadingMoment r X/r a-2*tau*r a
  have he (a : Fin m) : F a=F i := hmin.row_gradient_eq hm hr hs hX hXS tau hpsi a i
  have hmean : (∑ a,r a*F a)=F i := by
    simp_rw [he]
    rw [← Finset.sum_mul,hs,one_mul]
  have hprod (a : Fin m) : r a*(endpointLeadingMoment r X/r a)=endpointLeadingMoment r X :=
    mul_div_cancel₀ _ (hr a).ne'
  have hnorm := endpointLeading_rowDerivative_sum hm r X (fun a => (hr a).le) hs hX hXS
  dsimp only [F] at hmean
  simp only [mul_sub,Finset.sum_sub_distrib,hprod,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hmean
  rw [hnorm] at hmean
  have hsquare : (∑ a,r a*(2*tau*r a))=2*tau*∑ a,r a^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  rw [hsquare] at hmean
  linarith

end DittertRybin
