import DR.Endpoint.BoundaryPermanent

/-! The quantitative boundary-permanent ratio from Pang, equation (12).
The scalar argument here uses a proved cubic Bernoulli lower bound instead
of a logarithmic power-series expansion. -/

namespace DittertRybin

theorem boundaryPermanentRatio_succ_succ {n : ℕ} (hn : 1 ≤ n) :
    boundaryPermanentRatio (n+2) =
      (1-1/((n : ℝ)+1)^2)^(n+1)*(((n : ℝ)+1)/n) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn1 : (n : ℝ)+1 ≠ 0 := by positivity
  have hn2 : (n : ℝ)+2 ≠ 0 := by positivity
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hb : 1-1/((n : ℝ)+1)^2 = (n : ℝ)*((n : ℝ)+2)/((n : ℝ)+1)^2 := by
    field_simp
    ring
  rw [boundaryPermanentRatio,boundaryPermanentFloor_succ_succ,hb]
  simp only [dittertConstant,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
    Nat.cast_ofNat,pow_succ,div_pow,mul_pow]
  field_simp
  ring_nf

/-- A finite Bernoulli remainder bound, valid on the entire unit interval. -/
theorem boundary_bernoulli_cubic_lower {m : ℕ} (hm : 2 ≤ m) {t : ℝ}
    (_ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    1-(m : ℝ)*t+(m : ℝ)*(m-1)/2*t^2-(m : ℝ)*(m-1)*(m-2)/6*t^3 ≤ (1-t)^m := by
  induction m,hm using Nat.le_induction with
  | base => norm_num; nlinarith
  | @succ m hm ih =>
    have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have hmul := mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr ht1)
    have hrem : 0 ≤ (m : ℝ)*(m-1)*(m-2)*t^4 := by
      apply mul_nonneg
      · exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
      · positivity
    rw [pow_succ (1-t) m]
    push_cast
    nlinarith only [hmul,hrem]

/-- The relative gap exceeds the elementary inverse-square lower bound. -/
theorem boundaryPermanentRatio_sub_one_lower {n : ℕ} (hn : 4 ≤ n) :
    1/(3*((n : ℝ)-1)^2) < boundaryPermanentRatio n-1 := by
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le (show 2 ≤ n by omega)
  rw [Nat.add_comm] at hk
  subst n
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
  have hk0 : (k : ℝ) ≠ 0 := by linarith
  have hk1 : (k : ℝ)+1 ≠ 0 := by positivity
  have ht0 : 0 ≤ 1/((k : ℝ)+1)^2 := by positivity
  have ht1 : 1/((k : ℝ)+1)^2 ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hb := boundary_bernoulli_cubic_lower (by omega : 2 ≤ k+1) ht0 ht1
  have hd : 0 < 1-1/((k : ℝ)+1) := by
    apply sub_pos.mpr
    apply (div_lt_one (by positivity)).mpr
    linarith
  have he : (1-((k : ℝ)+1)*(1/((k : ℝ)+1)^2)+
      ((k : ℝ)+1)*k/2*(1/((k : ℝ)+1)^2)^2-
      ((k : ℝ)+1)*k*(k-1)/6*(1/((k : ℝ)+1)^2)^3) -
      (1-1/((k : ℝ)+1))*(1+1/(3*((k : ℝ)+1)^2)) =
        (k : ℝ)*(((k : ℝ)+1)^2-((k : ℝ)+1)+2)/(6*((k : ℝ)+1)^5) := by
    field_simp
    ring
  have hpos : 0 < (k : ℝ)*(((k : ℝ)+1)^2-((k : ℝ)+1)+2)/(6*((k : ℝ)+1)^5) := by
    apply div_pos
    · apply mul_pos (by linarith)
      nlinarith
    · positivity
  have hstrict : (1-1/((k : ℝ)+1))*(1+1/(3*((k : ℝ)+1)^2)) <
      (1-1/((k : ℝ)+1)^2)^(k+1) := by
    push_cast at hb
    nlinarith only [hb,he,hpos]
  rw [boundaryPermanentRatio_succ_succ (by omega)]
  have hdiv : 1+1/(3*((k : ℝ)+1)^2) <
      (1-1/((k : ℝ)+1)^2)^(k+1)/(1-1/((k : ℝ)+1)) := by
    apply (lt_div_iff₀ hd).mpr
    simpa only [mul_comm] using hstrict
  have hid : 1/(1-1/((k : ℝ)+1)) = ((k : ℝ)+1)/k := by
    field_simp
    simp [hk0]
  have hid2 (p : ℝ) : p/(1-1/((k : ℝ)+1)) = p*(((k : ℝ)+1)/k) := by
    rw [div_eq_mul_inv,←one_div,hid]
  rw [hid2] at hdiv
  push_cast
  rw [show (k : ℝ)+2-1 = k+1 by ring]
  linarith only [hdiv]

theorem boundaryPermanentRatio_upper {n : ℕ} (hn : 3 ≤ n) :
    boundaryPermanentRatio n < ((n : ℝ)-1)/((n : ℝ)-2) := by
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le (show 2 ≤ n by omega)
  rw [Nat.add_comm] at hk
  subst n
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hb0 : 0 ≤ 1-1/((k : ℝ)+1)^2 := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hb1 : 1-1/((k : ℝ)+1)^2 < 1 := by
    have h : 0 < 1/((k : ℝ)+1)^2 := by positivity
    linarith
  have hp := pow_lt_one₀ hb0 hb1 (show k+1 ≠ 0 by omega)
  have hq : 0 < ((k : ℝ)+1)/k := div_pos (by positivity) (by linarith)
  have hh := mul_lt_mul_of_pos_right hp hq
  rw [boundaryPermanentRatio_succ_succ (by omega)]
  push_cast
  rw [show (k : ℝ)+2-1 = k+1 by ring,show (k : ℝ)+2-2 = k by ring]
  simpa only [one_mul] using hh

/-- Pang's equation (12), derived from the internally proved boundary ratio.
No asymptotic estimate or finite-dimensional extrapolation is used. -/
theorem boundaryPermanentRatio_gap {n : ℕ} (hn : 18 ≤ n) :
    (16/17 : ℝ)^2/(3*((n : ℝ)-1)^2) <
      (boundaryPermanentRatio n-1)/(boundaryPermanentRatio n)^2 := by
  have hnR : (18 : ℝ) ≤ n := by exact_mod_cast hn
  have hlow := boundaryPermanentRatio_sub_one_lower (by omega : 4 ≤ n)
  have hn1 : 0 < (n : ℝ)-1 := by linarith
  have hlpos : 0 < 1/(3*((n : ℝ)-1)^2) := by positivity
  have hkpos : 0 < boundaryPermanentRatio n := by linarith
  have hupper : boundaryPermanentRatio n < (17/16 : ℝ) := by
    apply (boundaryPermanentRatio_upper (by omega : 3 ≤ n)).trans_le
    apply (div_le_iff₀ (by linarith : 0 < (n : ℝ)-2)).mpr
    linarith
  have hsq := pow_le_pow_left₀ hkpos.le hupper.le 2
  apply (lt_div_iff₀ (pow_pos hkpos 2)).mpr
  apply lt_of_le_of_lt _ hlow
  calc
    (16/17 : ℝ)^2/(3*((n : ℝ)-1)^2)*(boundaryPermanentRatio n)^2 ≤
        (16/17 : ℝ)^2/(3*((n : ℝ)-1)^2)*(17/16 : ℝ)^2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 1/(3*((n : ℝ)-1)^2) := by ring

end DittertRybin
