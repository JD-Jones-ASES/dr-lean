import DR.Endpoint.DoubleRecurrence

/-! Common polynomial weights for the two exact doubled-endpoint criteria.
The dimension recurrences are genuine all-integer induction steps; only the
initial comparisons are literal rational evaluations. -/

namespace DittertRybin

noncomputable def endpointDoubleBoundarySum (p m : ℕ) : ℝ :=
  (m : ℝ)^p * (2*(m : ℝ)-1)^2 * distinctUniformProbability (2*m) m +
    (m : ℝ)^p * (2*(m : ℝ)-1)^3 * dittertConstant m

theorem endpoint_double_weight_succ_le {m p q : ℕ} (hm : 80 ≤ m) (hpq : p+q ≤ 8) :
    ((m : ℝ)+1)^p * (2*((m : ℝ)+1)-1)^q ≤
      (6/5 : ℝ) * ((m : ℝ)^p * (2*(m : ℝ)-1)^q) := by
  have hmR : (80 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hb0 : 0 ≤ 2*(m : ℝ)-1 := by linarith
  have ha : (m : ℝ)+1 ≤ (80/79 : ℝ)*(m : ℝ) := by linarith
  have hb : 2*((m : ℝ)+1)-1 ≤ (80/79 : ℝ)*(2*(m : ℝ)-1) := by linarith
  have hp : (80/79 : ℝ)^(p+q) ≤ (80/79 : ℝ)^8 := by gcongr; norm_num
  have hsmall : (80/79 : ℝ)^(p+q) ≤ 6/5 := hp.trans (by norm_num)
  calc
    ((m : ℝ)+1)^p * (2*((m : ℝ)+1)-1)^q ≤
        ((80/79 : ℝ)*(m : ℝ))^p * ((80/79 : ℝ)*(2*(m : ℝ)-1))^q := by
      exact mul_le_mul (pow_le_pow_left₀ (by linarith) ha p)
        (pow_le_pow_left₀ (by linarith) hb q) (pow_nonneg (by linarith) _)
        (pow_nonneg (by positivity) _)
    _ = (80/79 : ℝ)^(p+q) * ((m : ℝ)^p * (2*(m : ℝ)-1)^q) := by
      rw [pow_add, mul_pow, mul_pow]
      ring
    _ ≤ (6/5 : ℝ) * ((m : ℝ)^p * (2*(m : ℝ)-1)^q) :=
      mul_le_mul_of_nonneg_right hsmall (mul_nonneg (pow_nonneg hm0 _) (pow_nonneg hb0 _))

theorem endpoint_double_weighted_decay {m p q : ℕ} (hm : 80 ≤ m) (hpq : p+q ≤ 8)
    {x y : ℝ} (_hx : 0 ≤ x) (hy : 0 ≤ y) (hstep : y ≤ (5/6 : ℝ)*x) :
    ((m : ℝ)+1)^p * (2*((m : ℝ)+1)-1)^q * y ≤
      (m : ℝ)^p * (2*(m : ℝ)-1)^q * x := by
  have hmR : (80 : ℝ) ≤ m := by exact_mod_cast hm
  have hb : 0 ≤ 2*(m : ℝ)-1 := by linarith
  calc
    ((m : ℝ)+1)^p * (2*((m : ℝ)+1)-1)^q * y ≤
        ((6/5 : ℝ)*((m : ℝ)^p*(2*(m : ℝ)-1)^q)) * ((5/6 : ℝ)*x) :=
      mul_le_mul (endpoint_double_weight_succ_le hm hpq) hstep hy (by positivity)
    _ = (m : ℝ)^p*(2*(m : ℝ)-1)^q*x := by ring

theorem endpointDoubleBoundarySum_succ_le {m p : ℕ} (hm : 80 ≤ m) (hp : p ≤ 5) :
    endpointDoubleBoundarySum p (m+1) ≤ endpointDoubleBoundarySum p m := by
  have hb := (distinctUniformProbability_pos (by omega : 0 < 2*m) (by omega : m ≤ 2*m)).le
  have hbnext := (distinctUniformProbability_pos (by omega : 0 < 2*(m+1))
    (by omega : m+1 ≤ 2*(m+1))).le
  have ha := (endpoint_a_pos (by omega : 0 < m)).le
  have hanext := (endpoint_a_pos (by omega : 0 < m+1)).le
  have hstepa : dittertConstant (m+1) ≤ (5/6 : ℝ)*dittertConstant m := by
    have hhalf := distinctUniformProbability_endpoint_succ_le_half (by omega : 1 ≤ m)
    rw [distinctUniformProbability_self, distinctUniformProbability_self] at hhalf
    linarith
  have hX := endpoint_double_weighted_decay (p := p) (q := 2) hm (by omega) hb hbnext
    (distinctUniformProbability_double_succ_le (by omega))
  have hY := endpoint_double_weighted_decay (p := p) (q := 3) hm (by omega) ha hanext hstepa
  simpa only [endpointDoubleBoundarySum, Nat.cast_add, Nat.cast_one] using add_le_add hX hY

theorem endpointDoubleBoundarySum_le_base {M m p : ℕ} (hM : 80 ≤ M)
    (hm : M ≤ m) (hp : p ≤ 5) :
    endpointDoubleBoundarySum p m ≤ endpointDoubleBoundarySum p M := by
  induction m, hm using Nat.le_induction with
  | base => exact le_rfl
  | @succ m hm ih => exact (endpointDoubleBoundarySum_succ_le (hM.trans hm) hp).trans ih

end DittertRybin
