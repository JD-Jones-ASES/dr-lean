import DR.Endpoint.DoubleRecurrence

/-! Exact consecutive-dimension endpoint scalar bounds from m=30 onward.
The factorial half-decay dominates every polynomial weight of total degree
eight; induction therefore propagates one exact rational base to all m≥30. -/

namespace DittertRybin

noncomputable def endpointConsecutiveBoundarySum (m : ℕ) : ℝ :=
  (m : ℝ)^5*((m : ℝ)+1)^3*dittertConstant (m+1) +
    (m : ℝ)^6*((m : ℝ)+1)^2*dittertConstant m

/-- Exact adjacent-column avoidance, including the endpoint factorial factor. -/
theorem distinctUniformProbability_consecutive (m : ℕ) :
    distinctUniformProbability (m+1) m = ((m : ℝ)+1)*dittertConstant (m+1) := by
  rw [distinctUniformProbability_factorial (by omega : m ≤ m+1)]
  simp only [Nat.add_sub_cancel_left, Nat.factorial_one, Nat.cast_one, one_mul,
    dittertConstant, Nat.cast_add, Nat.cast_one, pow_succ]
  have hm : (m : ℝ)+1 ≠ 0 := by positivity
  field_simp

theorem endpoint_consecutive_weight_succ_le {m p q : ℕ}
    (hm : 30 ≤ m) (hpq : p+q ≤ 8) :
    ((m : ℝ)+1)^p*((m : ℝ)+2)^q ≤
      2*((m : ℝ)^p*((m : ℝ)+1)^q) := by
  have hmR : (30 : ℝ) ≤ m := by exact_mod_cast hm
  have ha : (m : ℝ)+1 ≤ (31/30 : ℝ)*(m : ℝ) := by linarith
  have hb : (m : ℝ)+2 ≤ (31/30 : ℝ)*((m : ℝ)+1) := by linarith
  have hp : (31/30 : ℝ)^(p+q) ≤ (31/30 : ℝ)^8 := by gcongr; norm_num
  have hsmall : (31/30 : ℝ)^(p+q) ≤ 2 := hp.trans (by norm_num)
  calc
    ((m : ℝ)+1)^p*((m : ℝ)+2)^q ≤
        ((31/30 : ℝ)*(m : ℝ))^p*((31/30 : ℝ)*((m : ℝ)+1))^q := by
      exact mul_le_mul (pow_le_pow_left₀ (by linarith) ha p)
        (pow_le_pow_left₀ (by linarith) hb q) (pow_nonneg (by linarith) _)
        (pow_nonneg (by positivity) _)
    _ = (31/30 : ℝ)^(p+q)*((m : ℝ)^p*((m : ℝ)+1)^q) := by
      rw [pow_add, mul_pow, mul_pow]
      ring
    _ ≤ 2*((m : ℝ)^p*((m : ℝ)+1)^q) :=
      mul_le_mul_of_nonneg_right hsmall (by positivity)

theorem endpoint_consecutive_weighted_decay {m p q : ℕ}
    (hm : 30 ≤ m) (hpq : p+q ≤ 8) {x y : ℝ}
    (hy : 0 ≤ y) (hstep : y ≤ x/2) :
    ((m : ℝ)+1)^p*((m : ℝ)+2)^q*y ≤ (m : ℝ)^p*((m : ℝ)+1)^q*x := by
  calc
    ((m : ℝ)+1)^p*((m : ℝ)+2)^q*y ≤
        (2*((m : ℝ)^p*((m : ℝ)+1)^q))*(x/2) :=
      mul_le_mul (endpoint_consecutive_weight_succ_le hm hpq) hstep hy (by positivity)
    _ = (m : ℝ)^p*((m : ℝ)+1)^q*x := by ring

theorem endpointConsecutiveBoundarySum_succ_le {m : ℕ} (hm : 30 ≤ m) :
    endpointConsecutiveBoundarySum (m+1) ≤ endpointConsecutiveBoundarySum m := by
  have ha := (endpoint_a_pos (by omega : 0 < m+1)).le
  have hanext := (endpoint_a_pos (by omega : 0 < m+1+1)).le
  have hs0 := distinctUniformProbability_endpoint_succ_le_half (by omega : 1 ≤ m)
  have hs1 := distinctUniformProbability_endpoint_succ_le_half (by omega : 1 ≤ m+1)
  rw [distinctUniformProbability_self, distinctUniformProbability_self] at hs0 hs1
  have hX := endpoint_consecutive_weighted_decay (p := 5) (q := 3) hm (by decide) hanext hs1
  have hY := endpoint_consecutive_weighted_decay (p := 6) (q := 2) hm (by decide) ha hs0
  simpa only [endpointConsecutiveBoundarySum, Nat.cast_add, Nat.cast_one, add_assoc,
    show (1 : ℝ)+1 = 2 by norm_num] using add_le_add hX hY

set_option maxRecDepth 2048 in
theorem endpoint_consecutive_parameter_base :
    endpointConsecutiveBoundarySum 30 < (3/4 : ℝ)*(512/289) := by
  norm_num [endpointConsecutiveBoundarySum, dittertConstant, Nat.factorial]

theorem endpointConsecutiveBoundarySum_lt {m : ℕ} (hm : 30 ≤ m) :
    endpointConsecutiveBoundarySum m < (512/289 : ℝ) := by
  have hle : endpointConsecutiveBoundarySum m ≤ endpointConsecutiveBoundarySum 30 := by
    induction m, hm using Nat.le_induction with
    | base => exact le_rfl
    | @succ m hm ih => exact (endpointConsecutiveBoundarySum_succ_le hm).trans ih
  exact (hle.trans_lt endpoint_consecutive_parameter_base).trans (by norm_num)

/-- The actual gain-one scalar criterion throughout the infinite consecutive tail. -/
theorem endpoint_consecutive_parameter_criterion {m : ℕ} (hm : 30 ≤ m) :
    distinctUniformProbability (m+1) m + (((m+1 : ℕ) : ℝ)-1)*dittertConstant m <
      (512/289 : ℝ) / ((m : ℝ)^3*((m+1 : ℕ) : ℝ)^2*(((m+1 : ℕ) : ℝ)-1)^2) := by
  have hmR : (30 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  apply (lt_div_iff₀ (by positivity : 0 < (m : ℝ)^3*((m : ℝ)+1)^2*(m : ℝ)^2)).mpr
  rw [distinctUniformProbability_consecutive]
  have heq : (((m : ℝ)+1)*dittertConstant (m+1)+(m : ℝ)*dittertConstant m)*
      ((m : ℝ)^3*((m : ℝ)+1)^2*(m : ℝ)^2) = endpointConsecutiveBoundarySum m := by
    unfold endpointConsecutiveBoundarySum
    ring
  rw [heq]
  exact endpointConsecutiveBoundarySum_lt hm

end DittertRybin
