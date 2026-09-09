import DR.Rectangular.OrderThreeFourRowGauge

namespace DittertRybin.Tests
open scoped BigOperators

-- Zero row mass has a negative supporting polynomial but a strictly positive weight.
example : orderThreeFourRowGauge 0 = 0 ∧ 0 < orderThreeFourRowWeight 0 := by
  norm_num [orderThreeFourRowGauge, orderThreeFourRowWeight]

example : (16*(1:ℝ)^2+88*1-3)/32 ≤ Real.sqrt 10 * orderThreeFourRowGauge 1 :=
  orderThreeFourRowGauge_support (by norm_num) (by norm_num)

-- The support statement is confined to probability coordinates; t=2 is a negative control.
example : ¬ ((16*(2:ℝ)^2+88*2-3)/32 ≤ Real.sqrt 10 * orderThreeFourRowGauge 2) := by
  have h10 : Real.sqrt (10:ℝ)^2=10 := Real.sq_sqrt (by norm_num)
  have hthird : Real.sqrt (1/3:ℝ)^2=1/3 := Real.sq_sqrt (by norm_num)
  have hprod : (Real.sqrt 10 * (2*Real.sqrt (1/3:ℝ)))^2=40/3 := by
    rw [mul_pow,mul_pow,h10,hthird]
    norm_num
  have hw : orderThreeFourRowWeight 2 = Real.sqrt (1/3:ℝ) := by
    unfold orderThreeFourRowWeight
    congr 1
    norm_num
  rw [orderThreeFourRowGauge, hw]
  norm_num only
  intro h
  have hm := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 237/32) h 2
  rw [hprod] at hm
  norm_num at hm

example (r : Fin 4 → ℝ) (hr : ∀ i,0 ≤ r i) (hmass : ∑ i,r i=1) :
    5/8+orderThreeFourRowVariance r/4 ≤ (∑ i,orderThreeFourRowGauge (r i))^2 :=
  orderThreeFourRowGauge_sum_sq_lower r hr hmass

#print axioms orderThreeFourRowGauge_support
#print axioms orderThreeFourRowGauge_sum_lower
#print axioms orderThreeFourRowGauge_sum_sq_lower
end DittertRybin.Tests
