import DR.Endpoint.TwoZeroLogTail

namespace DittertRybin.Tests

-- Both signs of the logarithmic expansions retain their equality boundary.
example : (0 : ℝ) ≤ Real.log (1-0) ∧ (0 : ℝ) ≤ Real.log (1+0) := by norm_num

example {x c : ℝ} (hx : 0 ≤ x) (hxc : x ≤ c) (hc : c < 1) :
    -x-x^2/2-x^3/3-x^4/(4*(1-c)) ≤ Real.log (1-x) :=
  twoZero_log_one_sub_quartic_cap hx hxc hc

example : twoZeroY 0=1 ∧ twoZeroZ 0=1 ∧ twoZeroLogPolynomial 0=3 := by
  norm_num [twoZeroY,twoZeroZ,twoZeroLogPolynomial]

-- The source endpoint agrees exactly; the lighter grouping proof has margin.
example : twoZeroLogPolynomial (1/25) =
    (7251476123504102317506/23283064365386962890625 : ℝ) ∧
    (0 : ℝ) < 3-71/25-46/25^3-14568/25^5 := by
  norm_num [twoZeroLogPolynomial]

-- Extending the interval from 1/25 to 1/20 would invalidate positivity.
example : twoZeroLogPolynomial (1/20) < 0 := by norm_num [twoZeroLogPolynomial]

-- A denominator pole cannot be silently admitted in the exact identity.
example : ¬((1/(1/2 : ℝ)-2)*twoZeroLogLowerY (1/2)+twoZeroLogLowerZ (1/2)+
    (2/(1/2 : ℝ))*twoZeroLogLowerPlus (1/2)-(1/2 : ℝ)^2/4 =
      (1/2 : ℝ)^2*twoZeroLogPolynomial (1/2)/(12*(1-3*(1/2 : ℝ)))) := by
  norm_num [twoZeroLogLowerY,twoZeroLogLowerZ,twoZeroLogLowerPlus,twoZeroY,twoZeroZ,
    twoZeroLogPolynomial]

example : (1+1/(4*25^2) : ℝ) < twoZeroCoarseRatio 25 :=
  twoZeroCoarseRatio_gt (by norm_num)

-- The ratio identity is exact before the tail threshold; the tail inequality is not.
example : ¬(1 : ℝ) < twoZeroCoarseRatio 4 := by
  norm_num [twoZeroCoarseRatio,twoZeroY,twoZeroZ]

example : ((4).factorial : ℝ)*(twoZeroX 4 (7/32))^2*twoZeroH 4 (1/4) =
    boundaryPermanentFloor 6*twoZeroCoarseRatio 4 := by
  have h := twoZeroCoarseRatio_normalization (by norm_num : 2 ≤ 4)
  norm_num at h
  exact h

-- Confusing the one-zero boundary reference with gamma changes the floor.
example : ¬((4).factorial : ℝ)*(twoZeroX 4 (7/32))^2*twoZeroH 4 (1/4) =
    dittertConstant 6*twoZeroCoarseRatio 4 := by
  norm_num [twoZeroX,twoZeroH,dittertConstant,twoZeroCoarseRatio,twoZeroY,twoZeroZ,Nat.factorial]

-- Both exceptional diagonal entries may vanish in the first tail dimension.
example : boundaryPermanentFloor 27*(1+1/(4*25^2)) <
    twoZeroReducedPermanent 25 (1/25) (1/25) := by
  exact twoZeroReducedPermanent_tail_gap (by norm_num : 25 ≤ 25)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example {m : ℕ} (hm : 25 ≤ m) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haM : a ≤ 1/(m : ℝ)) (hbM : b ≤ 1/(m : ℝ)) :
    boundaryPermanentFloor (m+2)*(1+1/(4*(m : ℝ)^2)) < twoZeroReducedPermanent m a b :=
  twoZeroReducedPermanent_tail_gap hm ha hb haM hbM

#print axioms twoZero_log_one_sub_cubic
#print axioms twoZero_log_one_sub_quartic
#print axioms twoZero_log_one_add_quartic
#print axioms twoZeroLogPolynomial_pos
#print axioms twoZeroYZ_caps
#print axioms twoZeroLogLower_identity
#print axioms twoZero_logarithmic_margin
#print axioms twoZeroCoarseRatio_gt
#print axioms twoZeroCoarseRatio_normalization
#print axioms twoZeroReducedPermanent_tail_gap
end DittertRybin.Tests
