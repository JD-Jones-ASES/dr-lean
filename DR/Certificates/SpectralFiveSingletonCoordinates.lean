import DR.Certificates.SpectralFiveGuards

/-! Unit-box coordinates for the actual singleton marginal envelope, including t=0. -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section

theorem nonnegative_interval_unit_coordinate {c u : ℝ}
    (hc : 0 ≤ c) (hu : 0 ≤ u) (huc : u ≤ c) :
    ∃ x : ℝ, 0 ≤ x ∧ x ≤ 1 ∧ u = c*x := by
  rcases hc.eq_or_lt with hc | hc
  · refine ⟨0, by norm_num, by norm_num, ?_⟩
    simp only [mul_zero]
    linarith
  · refine ⟨u/c, div_nonneg hu hc.le, (div_le_one hc).mpr huc, ?_⟩
    exact (mul_div_cancel₀ u hc.ne').symm

theorem singleton_unit_coordinates {t u v : ℝ}
    (ht : 0 ≤ t) (hu : 0 ≤ u) (hu1 : u ≤ (23/50)*t)
    (hv : 0 ≤ v) (hv1 : v ≤ t/2) :
    ∃ x y : ℝ, (0 ≤ x ∧ x ≤ 1) ∧ (0 ≤ y ∧ y ≤ 1) ∧
      u = (23/50)*t*x ∧ v = (1/2)*t*y := by
  obtain ⟨x, hx, hx1, huEq⟩ := nonnegative_interval_unit_coordinate (by positivity) hu hu1
  obtain ⟨y, hy, hy1, hvEq⟩ := nonnegative_interval_unit_coordinate (by positivity) hv hv1
  refine ⟨x, y, ⟨hx,hx1⟩, ⟨hy,hy1⟩, huEq, ?_⟩
  rw [hvEq]
  ring

end
end DittertRybin.Certificates.SpectralFiveSingleton
