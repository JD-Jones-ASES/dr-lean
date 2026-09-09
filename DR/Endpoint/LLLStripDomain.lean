import DR.Endpoint.UniformAvoidanceBound

/-! Exact equivalence of the source's real-power lower cutoff and the
integer squared cutoff used by the release theorem. -/
namespace DittertRybin

theorem endpoint_lll_lower_edge_iff (m n : ℕ) :
    (64:ℝ)*(m:ℝ)^(3/2:ℝ)≤(n:ℝ) ↔ 4096*m^3≤n^2 := by
  have hp : ((m:ℝ)^(3/2:ℝ))^2=(m:ℝ)^3 := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg m) (3/2) 2]
    norm_num
  have hs : ((64:ℝ)*(m:ℝ)^(3/2:ℝ))^2=(4096:ℝ)*(m:ℝ)^3 := by
    rw [mul_pow,hp]
    norm_num
  have hleft : 0≤(64:ℝ)*(m:ℝ)^(3/2:ℝ) := by positivity
  constructor
  · intro h
    have hsq := (sq_le_sq₀ hleft (Nat.cast_nonneg n)).mpr h
    rw [hs] at hsq
    exact_mod_cast hsq
  · intro h
    apply (sq_le_sq₀ hleft (Nat.cast_nonneg n)).mp
    rw [hs]
    exact_mod_cast h

end DittertRybin
