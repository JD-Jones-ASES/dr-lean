import DR.Rectangular.ThreeRowTwoDoubletNormal

namespace DittertRybin.Tests

-- Without the residual majority p>r the two positive equations and missing inequality can hold.
example : (1+1+4 : ℝ)*(5/8)+(1+1)*(5/8)=(1+4)*1 ∧
    (1+1 : ℝ)*(5/8)+(1+1+4)*(5/8)=(1+4)*1 ∧
    0 < (1+4 : ℝ)*(5/8)+(1+4)*(5/8)-(1+1+4)*1 ∧ (5/8 : ℝ)<1 := by norm_num

-- The positive equations alone do not replace the full-simplex derivative inequality.
-- The second coordinate is negative, which is permitted for a column difference.
example : (2+1+1 : ℝ)*(6/7)+(2+1)*(-1/7)=(2+1)*1 ∧
    (2+1 : ℝ)*(6/7)+(2+1+1)*(-1/7)=(1+1)*1 ∧
    (2+1 : ℝ)*(6/7)+(1+1)*(-1/7)-(2+1+1)*1<0 ∧
    (6/7 : ℝ)<1 ∧ (-1/7 : ℝ)<1 := by norm_num

-- Z=0 permits the homogeneous zero solution, so conditioning on a full column matters.
example : (2+1+1 : ℝ)*0+(2+1)*0=(2+1)*0 ∧
    (2+1 : ℝ)*0+(2+1+1)*0=(1+1)*0 ∧ 0 ≤ (2+1 : ℝ)*0+(1+1)*0-(2+1+1)*0 := by norm_num

example {p q r x y Z : ℝ} (hp : r < p) (hq : 0 < q) (hr : 0 < r) (hZ : 0 < Z)
    (hx : x < Z) (hy : y < Z)
    (h1 : (p+q+r)*x+(p+q)*y=(p+r)*Z)
    (h2 : (p+q)*x+(p+q+r)*y=(q+r)*Z) :
    (p+r)*x+(q+r)*y-(p+q+r)*Z < 0 := by
  by_contra h
  exact threeRow_two_doublet_inverse_impossible hp hq hr hZ hx hy h1 h2 (le_of_not_gt h)

example {n : ℕ} {P : Board 3 n} (hP : IsProbability P) (hmax : IsSeparationGlobalMax P 3)
    (hn : 3 ≤ n) (i h : Fin 3) (hih : i ≠ h) (a b : Fin n)
    (ha : ThreeRowDoublet P i a) (hb : ThreeRowDoublet P h b)
    (htypes : ∀ r j, ThreeRowDoublet P r j → r=i ∨ r=h) : False :=
  hmax.threeRow_not_two_doublet_types hP hn i h hih a b ha hb htypes

#print axioms threeRow_two_doublet_inverse_impossible
#print axioms IsSeparationGlobalMax.threeRow_two_doublet_entry_order
#print axioms IsSeparationGlobalMax.threeRow_ordered_two_doublets_impossible
#print axioms IsSeparationGlobalMax.threeRow_not_two_doublet_types
end DittertRybin.Tests
