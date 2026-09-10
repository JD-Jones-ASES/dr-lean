import DR.Endpoint.ConsecutiveCutClosure
import DR.Endpoint.ConsecutiveLarge

/-! Full sharp consecutive rectangular endpoints: the exact finite active-cut
certificates cover 19 through 29, and the factorial recurrence covers every
integer dimension from 30 onward. -/

namespace DittertRybin

theorem uniform_maximum_consecutive_endpoint_finite {m : ℕ} (hm : 19 ≤ m) (hm' : m ≤ 29) :
    UniformMaximizer m (m+1) m ∧ UniformMaximizer (m+1) m m := by
  have hmain : UniformMaximizer m (m+1) m := by
    apply uniform_maximizer_of_all_global_positive (by omega) le_rfl (by omega)
    intro P hP hmax i j
    by_contra hn
    have hz : P i j = 0 := le_antisymm (le_of_not_gt hn) (hP.1 i j)
    have hcont := hmax (uniformBoard m (m+1)) (uniformBoard_isProbability (by omega) (by omega))
    rw [separationProbability_uniform (by omega) (by omega)] at hcont
    exact consecutive_boundary_contender_impossible hm hm' hP hcont ⟨i, j, hz⟩
  exact ⟨hmain, hmain.transpose⟩

/-- Uniform uniquely maximizes the endpoint success on every m by m+1
probability board, m at least 19, and on its transpose. -/
theorem uniform_maximum_consecutive_endpoint {m : ℕ} (hm : 19 ≤ m) :
    UniformMaximizer m (m+1) m ∧ UniformMaximizer (m+1) m m := by
  by_cases h : 30 ≤ m
  · exact uniform_maximum_consecutive_endpoint_of_thirty_le h
  · exact uniform_maximum_consecutive_endpoint_finite hm (by omega)

end DittertRybin
