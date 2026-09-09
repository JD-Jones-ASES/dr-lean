import DR.Rectangular.ThreeRowSingleDoubletScalar

namespace DittertRybin.Tests

-- The two positive-entry identities alone admit a nonuniform three-block point.
-- Its zero-entry derivative inequalities fail and are essential to exclusion.
example : ((2:ℝ)-1)*(2+4*1) = 2*(2+1) ∧
    (2-1)*(1*2+(3*2-2)*1) = 1*2*(2+1) ∧
    -(2+2*1)*2+2*(2+1)*(2-1) < 0 := by norm_num

-- The N≥3 boundary matters: S=T=1, b=d=1,c=2 satisfies all four conditions.
example : ((1:ℝ)-1)*(0+4*0) = 2*(0+0) ∧
    0 ≤ -(0+2*0)*2+2*(0+0)*(1-1) ∧
    (2-1)*(1*1+(3*1-2)*1) = 1*1*(1+1) ∧
    1*((3*1-2)*1+1*1) ≤ 1*(2-1)*(1+1) := by norm_num

-- Strict positivity of the full block is essential: d=0, S=1,T=2,b=c=1
-- satisfies the same displayed first-order equations and inequalities.
example : ((1:ℝ)-0)*(1+4*0) = 1*(1+0) ∧
    0 ≤ -(1+2*0)*1+2*(1+0)*(1-0) ∧
    (1-0)*(1*1+(3*2-2)*0) = 1*1*(1+0) ∧
    1*((3*1-2)*1+2*0) ≤ 2*(1-0)*(1+0) := by norm_num

-- Actual integer multiplicities are retained in the principal interface.
example {S T : ℕ} {b c d : ℝ} (hS : 1 ≤ S) (hT : 1 ≤ T) (hN : 3 ≤ S+T)
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hcol : (b-d)*(((T:ℝ)-1)*c+4*(((S:ℝ)-1)*b+((T:ℝ)-1)*d)) =
      c*(((T:ℝ)-1)*c+((S:ℝ)-1)*b+((T:ℝ)-1)*d))
    (hcolzero : 0 ≤ -(((T:ℝ)-1)*c+2*(((S:ℝ)-1)*b+((T:ℝ)-1)*d))*c +
      2*(((T:ℝ)-1)*c+((S:ℝ)-1)*b+((T:ℝ)-1)*d)*(b-d))
    (hrow : (c-d)*((S:ℝ)*b+(3*(T:ℝ)-2)*d) = (S:ℝ)*b*(b+d))
    (hrowzero : b*((3*(S:ℝ)-2)*b+(T:ℝ)*d) ≤ (T:ℝ)*(c-d)*(b+d)) : False :=
  threeRow_single_doublet_full_kkt_impossible hS hT hN hb hc hd hcol hcolzero hrow hrowzero

#print axioms threeRow_single_doublet_column_forces
#print axioms threeRow_single_doublet_quadratic_alternatives
#print axioms threeRow_single_doublet_mixed_impossible
#print axioms threeRow_single_doublet_strict_impossible
#print axioms threeRow_single_doublet_full_kkt_impossible
end DittertRybin.Tests
