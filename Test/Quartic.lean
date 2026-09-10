import DR.Endpoint.Quartic

namespace DittertRybin.Tests

-- The first permitted row count and exact closed column cutoff.
example : UniformMaximizer 16 1310720000 16 ∧ UniformMaximizer 1310720000 16 16 :=
  uniform_maximum_quartic_endpoint_strip (by decide) (by decide)

example : UniformMaximizer 20 3200000001 20 :=
  (uniform_maximum_quartic_endpoint_strip (by decide) (by decide)).1

example (P : Board 16 1310720000) (hP : IsProbability P) :
    separationProbability P 16≤uniformSeparationValue 16 1310720000 16 :=
  ((uniform_maximum_quartic_endpoint_strip (m:=16) (n:=1310720000)
    (by decide) (by decide)).1 P hP).1

example (P : Board 16 1310720000) (hP : IsProbability P) :
    separationProbability P 16=uniformSeparationValue 16 1310720000 16 ↔
      P=uniformBoard 16 1310720000 :=
  ((uniform_maximum_quartic_endpoint_strip (m:=16) (n:=1310720000)
    (by decide) (by decide)).1 P hP).2

example : ¬(16:ℕ)≤15 := by decide
example : ¬20000*(16:ℕ)^4≤1310719999 := by decide

-- A nonzero variance survives the scalar argument; the fourth power matters.
example : (2:ℝ)^2*(1/1000)<1/16 := by
  apply longColumn_linear_row_bound (M:=2) (N:=320000) (b:=1) <;> norm_num

example : ¬∀ v : ℝ, 0≤v → v<503*(1:ℝ)/100 → (2:ℝ)^2*v<1/16 := by
  intro h
  have hh := h 1 (by norm_num) (by norm_num)
  norm_num at hh

#print axioms longColumn_linear_row_bound
#print axioms endpoint_quartic_contender_caps
#print axioms uniform_maximum_quartic_endpoint_strip

end DittertRybin.Tests
