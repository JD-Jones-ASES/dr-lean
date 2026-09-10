import DR.Endpoint.BoundaryScalingScalars

/-! Exact scalar parameters for the arithmetic boundary-scaling criterion.
The common-divisor gain is retained as G^2. No cut or matrix assumption is
hidden in these inequalities. -/

namespace DittertRybin

theorem endpoint_scaling_parameter_bounds {M N G a b : ℝ}
    (hM : 3 ≤ M) (hN : 18 ≤ N) (hG : 1 ≤ G) (hGM : G ≤ M)
    (ha : 0 < a) (hb : 0 < b)
    (hcriterion : b+(N-1)*a < (512/289)*G^2/(M^3*N^2*(N-1)^2)) :
    let L := (2*M*N^2/(3*G^2))*(1+(N-1)*a/b)
    b < 1/4 ∧ 0 < L ∧ L*b < 1 ∧
      M^2*b*L/4 < (16/17 : ℝ)^2/(3*(N-1)^2) := by
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hG0 : 0 < G := by linarith
  have hN1 : 0 < N-1 := by linarith
  have hden : 0 < M^3*N^2*(N-1)^2 := by positivity
  let L := (2*M*N^2/(3*G^2))*(1+(N-1)*a/b)
  have hL : 0 < L := by dsimp [L]; positivity
  have hcr := (lt_div_iff₀ hden).mp hcriterion
  have hGsq : G^2 ≤ M^2 := pow_le_pow_left₀ hG0.le hGM 2
  have hN2 : 4 ≤ N^2 := by nlinarith
  have hNm2 : 1 ≤ (N-1)^2 := by nlinarith
  have hM3 : 3*M^2 ≤ M^3 := by nlinarith only [mul_le_mul_of_nonneg_right hM (sq_nonneg M)]
  have hbig : 12*M^2 ≤ M^3*N^2*(N-1)^2 := by
    calc
      12*M^2 = (3*M^2)*4*1 := by ring
      _ ≤ M^3*N^2*(N-1)^2 := by gcongr
  have hbquarter : b < 1/4 := by
    have hnumer : (512/289)*G^2 < (1/4)*(M^3*N^2*(N-1)^2) := by
      nlinarith only [hGsq, hbig, sq_pos_of_pos hM0]
    have hscalar : (512/289)*G^2/(M^3*N^2*(N-1)^2) < 1/4 :=
      (div_lt_iff₀ hden).mpr hnumer
    have hna : 0 < (N-1)*a := mul_pos hN1 ha
    linarith
  have hratio : M^2*b*L/4 = M^3*N^2*(b+(N-1)*a)/(6*G^2) := by
    dsimp [L]
    field_simp
    ring
  have htarget : M^2*b*L/4 < (16/17 : ℝ)^2/(3*(N-1)^2) := by
    rw [hratio]
    apply (div_lt_div_iff₀ (by positivity : 0 < 6*G^2)
      (by positivity : 0 < 3*(N-1)^2)).mpr
    nlinarith only [hcr]
  have hsmall : (16/17 : ℝ)^2/(3*(N-1)^2) < 1 := by
    apply (div_lt_one (by positivity : 0 < 3*(N-1)^2)).mpr
    nlinarith only [hNm2]
  have hLb : L*b < 1 := by
    have hpos := mul_pos hL hb
    have hm2 : 4 ≤ M^2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hm2 hpos.le
    nlinarith only [htarget.trans hsmall, hmul]
  exact ⟨hbquarter, hL, hLb, htarget⟩

end DittertRybin
