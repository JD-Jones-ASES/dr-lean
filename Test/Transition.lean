import DR.Endpoint.Transition

namespace DittertRybin.Tests
open scoped BigOperators

-- The generic closure includes a one-column board: there are no distinct
-- column pairs, and the separate exact row-product equality closes it.
example : UniformMaximizer 2 1 2 := by
  apply uniform_maximum_endpoint_of_contender_kernel (by decide) (by decide)
  intro P hP hcont a b hab
  exact False.elim (hab (Subsingleton.elim a b))

-- Both closed interval endpoints are included, at the actual dimension
-- threshold, in both orientations. No large sample space is evaluated.
example : UniformMaximizer (10^18) ((10^18)*(10^18-1)/20) (10^18) ∧
    UniformMaximizer ((10^18)*(10^18-1)/20) (10^18) (10^18) := by
  apply uniform_maximum_transition_endpoint <;> norm_num
example : UniformMaximizer (10^18) (10^40) (10^18) ∧
    UniformMaximizer (10^40) (10^18) (10^18) := by
  apply uniform_maximum_transition_endpoint <;> norm_num

-- Full closed-simplex sharp value and iff equality, with no row positivity,
-- collision-avoidance, kernel or stationary-condition hypothesis.
example {m n : ℕ} (hm : 10^18≤m) (hmn : m≤n)
    (hl : m*(m-1)≤20*n) (hu : n≤10000*m^2) (P : Board m n)
    (hP : ∀ i j,0≤P i j) (hmass : totalMass P=1) :
    separationProbability P m≤dittertConstant m+
      (1-dittertConstant m)*distinctUniformProbability n m ∧
    (separationProbability P m=dittertConstant m+
      (1-dittertConstant m)*distinctUniformProbability n m ↔ P=uniformBoard m n) := by
  have h := (uniform_maximum_transition_endpoint hm hmn hl hu).1 P ⟨hP,hmass⟩
  have hv : uniformSeparationValue m n m=dittertConstant m+
      (1-dittertConstant m)*distinctUniformProbability n m := by
    rw [uniformSeparationValue_rectangular_endpoint]
    ring
  simpa only [hv] using h

-- The actual retained kernel supplies its own positive avoidance law.
example {m n : ℕ} (hm : 10^18≤m) (hmn : m≤n)
    (hl : m*(m-1)≤20*n) (hu : n≤10000*m^2) (P : Board m n)
    (hP : IsProbability P) (hc : uniformSeparationValue m n m≤separationProbability P m)
    (a b : Fin n) (hab : a≠b) :
    (averagingKernel (eraseColumns P {a,b}) (m-2)).PosDef :=
  endpoint_transition_contender_kernel_posDef hm hmn hl hu hP hc a b hab

#print axioms endpoint_maximizer_equal_columns_of_kernel
#print axioms uniform_maximum_endpoint_of_contender_kernel
#print axioms endpoint_transition_contender_kernel_posDef
#print axioms uniform_maximum_transition_endpoint_forward
#print axioms uniform_maximum_transition_endpoint_transpose
#print axioms uniform_maximum_transition_endpoint
end DittertRybin.Tests
