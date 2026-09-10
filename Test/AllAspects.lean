import DR.Endpoint.AllAspects

namespace DittertRybin.Tests

-- Both the square boundary and arbitrarily long rectangles are included.
example : UniformMaximizer (10^18) (10^18) (10^18) ∧
    UniformMaximizer (10^18) (10^18) (10^18) :=
  uniform_maximum_large_endpoints (by decide) (by decide)
example : UniformMaximizer (10^18) (10^40+1) (10^18) :=
  (uniform_maximum_large_endpoints (m:=10^18) (n:=10^40+1) (by decide) (by decide)).1

-- Concrete points lie in the arithmetic, LLL, transition and quadratic intervals.
example : 22*((2*10^18:ℕ):ℝ)*Real.log ((10^18:ℕ):ℝ)≤
    ((10^18:ℕ):ℝ)*(((10^18:ℕ):ℝ)-1) :=
  endpoint_arithmetic_lll_overlap (m:=10^18) (n:=2*10^18) (by decide) (by decide) (by decide)
example : 4096*(10^18:ℕ)^3≤(10^30)^2 ∧ 20*10^30≤10^18*(10^18-1) := by decide
example : (10^18:ℕ)*(10^18-1)≤20*10^36 ∧ 10^36≤10000*(10^18)^2 := by decide
example : 10000*(10^18:ℕ)^2≤10^40 := by decide

-- There is no integer gap at the closed boundaries of the last two strips.
example : (10^18:ℕ)*(10^18-1)≤20*(10^18*(10^18-1)/20+1) := by decide
example : ¬(10^18:ℕ)≤10^18-1 := by decide

-- The displayed logarithmic estimate cannot be extended to all positive m.
example : ¬Real.log (1000000:ℝ)≤Real.sqrt (1000000:ℝ)/2816 := by
  have h := endpoint_arithmetic_log_gt_one (m:=1000000) (by decide)
  norm_num only [Nat.cast_ofNat] at h
  norm_num
  linarith

#print axioms endpoint_large_log_sqrt
#print axioms endpoint_arithmetic_lll_overlap
#print axioms uniform_maximum_large_endpoints

end DittertRybin.Tests
