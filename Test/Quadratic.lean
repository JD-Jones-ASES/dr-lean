import DR.Endpoint.Quadratic

namespace DittertRybin.Tests

example : UniformMaximizer 96 92160000 96 ∧ UniformMaximizer 92160000 96 96 :=
  uniform_maximum_quadratic_endpoint_strip (by decide) (by decide)

example : UniformMaximizer 100 100000001 100 :=
  (uniform_maximum_quadratic_endpoint_strip (by decide) (by decide)).1

example (P : Board 96 92160000) (hP : IsProbability P) :
    separationProbability P 96≤uniformSeparationValue 96 92160000 96 :=
  ((uniform_maximum_quadratic_endpoint_strip (m:=96) (n:=92160000)
    (by decide) (by decide)).1 P hP).1

example (P : Board 96 92160000) (hP : IsProbability P) :
    separationProbability P 96=uniformSeparationValue 96 92160000 96 ↔
      P=uniformBoard 96 92160000 :=
  ((uniform_maximum_quadratic_endpoint_strip (m:=96) (n:=92160000)
    (by decide) (by decide)).1 P hP).2

-- Neither numerical junction can be silently rounded down.
example : ¬(96:ℕ)≤95 := by decide
example : ¬10000*(96:ℕ)^2≤92159999 := by decide

example : 128*(16:ℝ)^3*dittertConstant 16≤1 := longColumn_alpha_weighted_le (by decide)
example : dittertConstant 16<1/625000 := longColumn_alpha_lt (by decide)
example : endpointColumnLossFactor 16=119 := by norm_num [endpointColumnLossFactor]

example : (1/100:ℝ)<1/16 := by
  apply longColumn_saturated_row_bound (M:=1) (N:=10000) (b:=1/3) <;> norm_num

-- Omitting the column cutoff invalidates the scalar row implication.
example : ¬∀ x : ℝ, 0≤x → x/(1+x)<503*(1/3)/100 → x<1/16 := by
  intro h
  have hh := h 1 (by norm_num) (by norm_num)
  norm_num at hh

#print axioms longColumn_alpha_weighted_le
#print axioms longColumn_contender_initial_loss
#print axioms endpoint_contender_longColumn_concentration
#print axioms longColumn_modulus_lt
#print axioms endpoint_quadratic_contender_caps
#print axioms uniform_maximum_quadratic_endpoint_strip

end DittertRybin.Tests
