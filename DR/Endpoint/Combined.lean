import DR.Endpoint.SmallRowConcentration
import DR.Endpoint.LongColumnClosureFive
import DR.Endpoint.Quadratic
import DR.Endpoint.Quartic

/-! The accepted all-m>=5 quadratic cutoff, assembled without widening its
range. Small rows use actual repeated-cell concentration and the sharper
retained coefficient; larger rows use the frozen quartic/quadratic strips. -/
namespace DittertRybin

theorem uniform_maximum_smallRow_endpoint_strip {m n : ℕ} (hm : 5≤m) (hmU : m≤15)
    (hn : 100000000000*m^2≤n) : UniformMaximizer m n m ∧ UniformMaximizer n m m := by
  have h := uniform_maximum_endpoint_of_longColumn_five_caps hm
    (by omega : 10000*m^2≤n)
    (fun P hP hcont => endpoint_smallRow_contender_caps hm hmU hn P hP hcont)
  exact ⟨h,h.transpose⟩

theorem combined_quartic_cutoff {m n : ℕ} (hm : m≤95) (hn : 100000000000*m^2≤n) :
    20000*m^4≤n := by
  have hm2 : m^2≤95^2 := Nat.pow_le_pow_left hm 2
  have hcut : 20000*m^4≤100000000000*m^2 := by
    calc
      20000*m^4=(20000*m^2)*m^2 := by ring
      _ ≤ (20000*95^2)*m^2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hm2)
      _ ≤ 100000000000*m^2 := Nat.mul_le_mul_right _ (by norm_num)
  exact hcut.trans hn

/-- The complete accepted combined endpoint range, both orientations,
with all nonnegative probability matrices and exact uniform equality. -/
theorem uniform_maximum_combined_endpoint_strip {m n : ℕ} (hm : 5≤m)
    (hn : 100000000000*m^2≤n) : UniformMaximizer m n m ∧ UniformMaximizer n m m := by
  by_cases h96 : 96≤m
  · exact uniform_maximum_quadratic_endpoint_strip h96 (by omega)
  by_cases h16 : 16≤m
  · exact uniform_maximum_quartic_endpoint_strip h16 (combined_quartic_cutoff (by omega) hn)
  · exact uniform_maximum_smallRow_endpoint_strip hm (by omega) hn

end DittertRybin
