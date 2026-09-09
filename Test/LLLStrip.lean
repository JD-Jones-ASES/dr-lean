import DR.Endpoint.LLLStrip

namespace DittertRybin.Tests
open scoped BigOperators

-- The accepted strip contains this exact nonempty instance. The production
-- theorem is applied without evaluating its enormous sample space.
example : UniformMaximizer (2^22) (2^39) (2^22) := by
  apply uniform_maximum_endpoint_lll_strip <;> norm_num
example : UniformMaximizer (2^39) (2^22) (2^22) := by
  apply uniform_maximum_endpoint_lll_strip_transpose <;> norm_num

example : UniformMaximizer (2^22) (2^39) (2^22) ∧
    UniformMaximizer (2^39) (2^22) (2^22) := by
  apply uniform_maximum_lll_endpoint <;> norm_num

example : (64:ℝ)*((2^22:ℕ):ℝ)^(3/2:ℝ)≤((2^39:ℕ):ℝ) := by
  rw [endpoint_lll_lower_edge_iff]
  norm_num
example : (64:ℝ)*(0:ℝ)^(3/2:ℝ)≤0 := by
  simpa only [Nat.cast_zero] using (endpoint_lll_lower_edge_iff 0 0).mpr (by norm_num)

-- Full explicit closed-simplex inequality and iff equality, with no
-- positive-entry, positive-row, collision-bound, or optimizer-shape premise.
example {m n : ℕ} (hm : 128≤m) (hl : 4096*m^3≤n^2)
    (hu : 20*n≤m*(m-1)) (P : Board m n)
    (hP : ∀ i j,0≤P i j) (hmass : totalMass P=1) :
    separationProbability P m≤dittertConstant m+
      (1-dittertConstant m)*distinctUniformProbability n m ∧
    (separationProbability P m=dittertConstant m+
      (1-dittertConstant m)*distinctUniformProbability n m ↔ P=uniformBoard m n) := by
  have h := uniform_maximum_endpoint_lll_strip hm hl hu P ⟨hP,hmass⟩
  have hv : uniformSeparationValue m n m=dittertConstant m+
      (1-dittertConstant m)*distinctUniformProbability n m := by
    rw [uniformSeparationValue_rectangular_endpoint]
    ring
  simpa only [hv] using h

-- The deleted-board PosDef theorem derives all collision and coefficient
-- assumptions from an actual full-probability contender.
example {m n : ℕ} (hm : 128≤m) (hl : 4096*m^3≤n^2)
    (hu : 20*n≤m*(m-1)) (P : Board m n) (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m≤separationProbability P m)
    (a b : Fin n) (hab : a≠b) :
    (averagingKernel (eraseColumns P {a,b}) (m-2)).PosDef :=
  endpoint_strip_contender_kernel_posDef hm hl hu hP hcont a b hab

-- The nominal minimum row count alone is not advertised as a covered
-- rectangle; both integer strip guards remain necessary premises.
example : ¬∃n:ℕ,4096*128^3≤n^2 ∧ 20*n≤128*(128-1) := by
  rintro ⟨n,hl,hu⟩
  have hn := endpoint_strip_n_ge (by norm_num : 1≤128) hl
  omega

#print axioms endpoint_strip_contender_kernel_posDef
#print axioms endpoint_strip_maximizer_equal_columns
#print axioms uniform_maximum_endpoint_lll_strip
#print axioms uniform_maximum_endpoint_lll_strip_transpose
#print axioms endpoint_lll_lower_edge_iff
#print axioms uniform_maximum_lll_endpoint
end DittertRybin.Tests
