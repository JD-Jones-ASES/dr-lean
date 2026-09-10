import DR.Endpoint.LeadingKernel

/-! Exact scalar estimates at a saturated-penalty minimum. These lemmas
consume the actual stationarity and moment identities separately proved
for the leading gauge; no minimum or matrix conclusion is assumed here. -/

namespace DittertRybin
open scoped BigOperators

theorem saturated_sqrt_cap {a : ℝ} (ha : 0 < a) (ha1 : a < 1/1000) :
    Real.sqrt (1-a) ≤ 1-a/2 ∧ Real.sqrt (1-a)+a/1000 < 1 := by
  have hrad : 0 ≤ 1-a := by linarith
  have hs := Real.sq_sqrt hrad
  have hsn := Real.sqrt_nonneg (1-a)
  have hr : 0 ≤ 1-a/2 := by linarith
  have hle : Real.sqrt (1-a) ≤ 1-a/2 := by nlinarith [sq_nonneg a]
  exact ⟨hle, by linarith⟩

/-- The weighted moment inequality forces a strictly positive defect. -/
theorem saturated_moment_lower {a G D : ℝ} (ha : 0 < a) (ha1 : a < 1/1000)
    (hG : 0 < G) (hcap : G ≤ Real.sqrt (1-a)+a/1000)
    (hCS : 1 ≤ G*(G+2*D)) : (499/1000 : ℝ)*a < D := by
  obtain ⟨hs, hs1⟩ := saturated_sqrt_cap ha ha1
  have hG1 : G < 1 := hcap.trans_lt hs1
  have hd : 1-G < D := by
    have hsq : 0 < (1-G)^2 := sq_pos_of_pos (by linarith)
    nlinarith only [hCS, hsq, hG]
  linarith

/-- The nonlinear penalty controls each pair, even for large variance. -/
theorem saturated_pair_penalty_cap {a M x t u v : ℝ}
    (ha : 0 ≤ a) (hM : 0 < M) (hx : 0 ≤ x)
    (ht : t = a*M^2/(1000*(1+x)^2))
    (hu : u^2 ≤ 2*(1+x)/M^2) (hv : v^2 ≤ 2*(1+x)/M^2) :
    2*t*u*v ≤ (4/1000 : ℝ)*a := by
  have hd : 0 < 1+x := by linarith
  have hM2 : 0 < M^2 := sq_pos_of_pos hM
  have huv : u*v ≤ 2*(1+x)/M^2 := by nlinarith [sq_nonneg (u-v)]
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have hh := mul_le_mul_of_nonneg_left huv (show 0 ≤ 2*t by positivity)
  have hid : 2*t*(2*(1+x)/M^2) = (4/1000 : ℝ)*a/(1+x) := by
    rw [ht]
    field_simp
    ring
  rw [hid] at hh
  have hlast : (4/1000 : ℝ)*a/(1+x) ≤ (4/1000 : ℝ)*a := by
    apply (div_le_iff₀ hd).mpr
    nlinarith only [mul_nonneg ha hx]
  simpa only [mul_assoc] using hh.trans hlast

/-- Subtracting the genuine stationarity equations gives this exact identity. -/
theorem saturated_stationarity_pair {u v t D A B c q : ℝ}
    (hu : u ≠ 0) (hv : v ≠ 0)
    (hA : A = c+2*t*(u-q)+D/u) (hB : B = c+2*t*(v-q)+D/v) :
    A-B = (D-2*t*u*v)*(1/u-1/v) := by
  rw [hA, hB]
  field_simp
  ring

/-- The exact reciprocal spread constant is 1184/121. -/
theorem saturated_reciprocal_spread {a D t u v A B C : ℝ}
    (ha : 0 < a) (hD : (499/1000 : ℝ)*a < D)
    (ht : 2*t*u*v ≤ (4/1000 : ℝ)*a)
    (hA : 1 ≤ A ∧ A ≤ C) (hB : 1 ≤ B ∧ B ≤ C)
    (hC : C-1 < (1332/275 : ℝ)*a)
    (hid : A-B = (D-2*t*u*v)*(1/u-1/v)) :
    |1/u-1/v| < (1184/121 : ℝ) := by
  have hcoef : (495/1000 : ℝ)*a < D-2*t*u*v := by linarith
  have hp : 0 < D-2*t*u*v := by linarith
  have hab : |A-B| ≤ C-1 := abs_le.mpr ⟨by linarith [hA.1,hB.2],by linarith [hA.2,hB.1]⟩
  rw [hid, abs_mul, abs_of_pos hp] at hab
  have hprod := hab.trans_lt hC
  have hzero := abs_nonneg (1/u-1/v)
  have hmul := mul_le_mul_of_nonneg_right hcoef.le hzero
  nlinarith only [hprod, hmul, ha]

/-- Exact shifted polynomial certificate for every real M≥96. -/
theorem saturated_variance_scalar_gap {M a : ℝ} (hM : 96 ≤ M) (ha : a < 1/1000) :
    (1184/121 : ℝ)^2*(M-1) < (1-a)*(M^2-(1184/121 : ℝ)^2) := by
  have hu : 0 ≤ M-96 := by linarith
  have hsq : 0 ≤ (M-96)^2 := sq_nonneg _
  have hid : ((999/1000 : ℝ)*(M^2-(1184/121 : ℝ)^2)-
      (1184/121 : ℝ)^2*(M-1))*14641000 =
      14626359*(M-96)^2+1406404928*(M-96)+219750400 := by ring
  have hstrict : (1184/121 : ℝ)^2*(M-1) <
      (999/1000 : ℝ)*(M^2-(1184/121 : ℝ)^2) := by nlinarith only [hid,hu,hsq]
  have hpos : 0 < M^2-(1184/121 : ℝ)^2 := by nlinarith only [hM]
  have hmul := mul_lt_mul_of_pos_right (show (999/1000 : ℝ)<1-a by linarith) hpos
  exact hstrict.trans hmul

end DittertRybin
