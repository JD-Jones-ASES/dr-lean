import DR.Square.SpectralPair
import DR.Square.MarginalDiscrepancy

/-!
# The stationary marginal envelope in order five

The inverse-variance budgets of the two marginal vectors are coupled by the
actual stationarity equations. Three exact bootstrap steps improve the
initial entropy envelope. No positive-cell or connectivity assumption is made.
The resulting envelope applies to every stationary contender in dimension five.
-/

namespace DittertRybin

open scoped BigOperators
open Set

noncomputable def fiveDeficitParameter (delta : ℝ) : ℝ := Real.sqrt (5 * delta / (1 - delta))

noncomputable def inverseVariance {n : ℕ} (r : Fin n → ℝ) : ℝ :=
  ∑ i, (r i - 1) ^ 2 / r i

theorem inverseVariance_nonneg {n : ℕ} (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) :
    0 ≤ inverseVariance r := Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hr i)

theorem fiveDeficitParameter_nonneg (delta : ℝ) : 0 ≤ fiveDeficitParameter delta :=
  Real.sqrt_nonneg _

theorem fiveDeficitParameter_sq {delta : ℝ} (hd0 : 0 ≤ delta) (hd1 : delta < 1) :
    fiveDeficitParameter delta ^ 2 = 5 * delta / (1 - delta) :=
  Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num) hd0) (by linarith))

theorem fiveDeficitParameter_lt_cap {delta : ℝ} (hd0 : 0 ≤ delta)
    (hdg : delta ≤ dittertConstant 5) : fiveDeficitParameter delta < 9 / 20 := by
  have hg : dittertConstant 5 = 24 / 625 := by norm_num [dittertConstant, Nat.factorial]
  have hd1 : delta < 1 := by rw [hg] at hdg; linarith
  have hs := fiveDeficitParameter_sq hd0 hd1
  have hm : 5 * delta / (1 - delta) ≤ 120 / 601 := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - delta)).mpr
    rw [hg] at hdg
    linarith
  nlinarith [fiveDeficitParameter_nonneg delta]

private theorem log_inverseVariance_hasDerivAt (m : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x => x - 1 - Real.log x - m / 2 * ((x - 1) ^ 2 / x))
      ((x - 1) * (2 * x - m * (x + 1)) / (2 * x ^ 2)) x := by
  have h := (((hasDerivAt_id x).sub_const 1).sub (Real.hasDerivAt_log hx.ne')).sub
    (((((hasDerivAt_id x).sub_const 1).pow 2).div (hasDerivAt_id x) hx.ne').const_mul (m / 2))
  convert h using 1 <;> try rfl
  simp only [id_eq, Pi.pow_apply]
  field_simp
  ring

/-- An elementary logarithmic lower bound, valid on the entire half-line x≥m. -/
theorem log_deficit_ge_inverseVariance {m x : ℝ} (hm : 0 < m) (hm1 : m ≤ 1)
    (hx : m ≤ x) : m / 2 * ((x - 1) ^ 2 / x) ≤ x - 1 - Real.log x := by
  let F := fun x : ℝ => x - 1 - Real.log x - m / 2 * ((x - 1) ^ 2 / x)
  have hF1 : F 1 = 0 := by simp [F]
  have hfactor {z : ℝ} (hz : m ≤ z) : 0 ≤ 2 * z - m * (z + 1) := by
    rcases le_total z 1 with hz1 | hz1
    · nlinarith [mul_nonneg (sub_nonneg.mpr hz) (by linarith : 0 ≤ z + 1), sq_nonneg (z - 1)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hm1) (by linarith : 0 ≤ z + 1)]
  rcases le_total 1 x with h1x | hx1
  · have hmono : MonotoneOn F (Icc 1 x) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 1 x)
      · intro z hz
        exact (log_inverseVariance_hasDerivAt m (by have := hz.1; linarith : 0 < z)).continuousAt.continuousWithinAt
      · intro z hz
        exact (log_inverseVariance_hasDerivAt m (by have := (interior_subset hz).1; linarith : 0 < z)).hasDerivWithinAt
      · intro z hz
        have hz1 := (interior_subset hz).1
        exact div_nonneg (mul_nonneg (by linarith) (hfactor (by linarith))) (by positivity)
    have h := hmono ⟨le_rfl, h1x⟩ ⟨h1x, le_rfl⟩ h1x
    rw [hF1] at h
    dsimp [F] at h
    linarith
  · have hanti : AntitoneOn F (Icc x 1) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc x 1)
      · intro z hz
        exact (log_inverseVariance_hasDerivAt m (by have := hz.1; linarith : 0 < z)).continuousAt.continuousWithinAt
      · intro z hz
        exact (log_inverseVariance_hasDerivAt m (by have := (interior_subset hz).1; linarith : 0 < z)).hasDerivWithinAt
      · intro z hz
        have hzlo := (interior_subset hz).1
        have hzhi := (interior_subset hz).2
        exact div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (by linarith) (hfactor (by linarith))) (by positivity)
    have h := hanti ⟨le_rfl, hx1⟩ ⟨hx1, le_rfl⟩ hx1
    rw [hF1] at h
    dsimp [F] at h
    linarith

/-- Summing the scalar lower bound uses only the marginal total and product. -/
theorem inverseVariance_log_budget {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (hsum : ∑ i, r i = n) {m : ℝ}
    (hm : 0 < m) (hm1 : m ≤ 1) (hmin : ∀ i, m ≤ r i) :
    m / 2 * inverseVariance r ≤ -Real.log (∏ i, r i) := by
  have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => log_deficit_ge_inverseVariance hm hm1 (hmin i)
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, hsum, sub_self, zero_sub] at h
  rw [Real.log_prod (fun i _ => (hr i).ne')]
  exact h

/-- Shared product deficit controls both inverse-variance totals together. -/
theorem inverseVariance_shared_budget {n : ℕ} (r c : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (hsumr : ∑ i, r i = n) (hsumc : ∑ j, c j = n)
    {rho sigma delta m : ℝ} (hR : ∏ i, r i = 1 - rho) (hC : ∏ j, c j = 1 - sigma)
    (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma) (hbudget : rho + sigma ≤ delta) (hd1 : delta < 1)
    (hm : 0 < m) (hm1 : m ≤ 1) (hminr : ∀ i, m ≤ r i) (hminc : ∀ j, m ≤ c j) :
    m / 2 * (inverseVariance r + inverseVariance c) ≤ delta / (1 - delta) := by
  have hrow := inverseVariance_log_budget r hr hsumr hm hm1 hminr
  have hcol := inverseVariance_log_budget c hc hsumc hm hm1 hminc
  rw [hR] at hrow
  rw [hC] at hcol
  have hlR := neg_log_one_sub_le hrho (by linarith : rho ≤ delta) hd1
  have hlC := neg_log_one_sub_le hsigma (by linarith : sigma ≤ delta) hd1
  have hb := div_le_div_of_nonneg_right hbudget (by linarith : 0 ≤ 1 - delta)
  rw [add_div] at hb
  linarith

/-- The actual stationary equations couple the two inverse-variance totals. -/
theorem stationary_inverseVariance_coupled {n : ℕ} (A : Board n n) (α β : ℝ)
    (hrow : ∀ i, α * (rowSum A i - 1) = -(∑ j, A i j * (colSum A j - 1) / colSum A j))
    (hcol : ∀ j, β * (colSum A j - 1) = -(∑ i, A i j * (rowSum A i - 1) / rowSum A i)) :
    α * inverseVariance (rowSum A) = β * inverseVariance (colSum A) := by
  have hR : α * inverseVariance (rowSum A) =
      -(∑ i, ∑ j, A i j * ((rowSum A i - 1) / rowSum A i) * ((colSum A j - 1) / colSum A j)) := by
    unfold inverseVariance
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = (α * (rowSum A i - 1)) * ((rowSum A i - 1) / rowSum A i) := by ring
      _ = _ := by rw [hrow, neg_mul, Finset.sum_mul]; congr 1; apply Finset.sum_congr rfl; intro j _; ring
  have hC : β * inverseVariance (colSum A) =
      -(∑ j, ∑ i, A i j * ((rowSum A i - 1) / rowSum A i) * ((colSum A j - 1) / colSum A j)) := by
    unfold inverseVariance
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = (β * (colSum A j - 1)) * ((colSum A j - 1) / colSum A j) := by ring
      _ = _ := by rw [hcol, neg_mul, Finset.sum_mul]; congr 1; apply Finset.sum_congr rfl; intro i _; ring
  rw [hR, hC, Finset.sum_comm]

/-- Weighted coordinate projection onto the zero-sum marginal deviations. -/
theorem five_coordinate_inverseVariance_bound (r : Fin 5 → ℝ)
    (hr : ∀ i, 0 < r i) (hsum : ∑ i, r i = 5) (i : Fin 5) :
    (r i - 1) ^ 2 ≤ r i * (5 - r i) * inverseVariance r / 5 := by
  let S := Finset.univ.erase i
  have hSne : S.Nonempty := by
    obtain ⟨j, hj⟩ := exists_ne i
    exact ⟨j, by simp [S, hj]⟩
  have hsumS : ∑ j ∈ S, r j = 5 - r i := by
    have h := Finset.sum_erase_add (s := Finset.univ) (f := r) (Finset.mem_univ i)
    rw [hsum] at h
    dsimp [S]
    linarith
  have hrempos : 0 < 5 - r i := by
    rw [← hsumS]
    exact Finset.sum_pos (fun j _ => hr j) hSne
  have hsumD : ∑ j ∈ S, (r j - 1) = 1 - r i := by
    rw [Finset.sum_sub_distrib, hsumS]
    have hcard : S.card = 4 := by simp [S]
    simp only [Finset.sum_const, hcard, nsmul_eq_mul]
    ring
  have hsumV : (∑ j ∈ S, (r j - 1) ^ 2 / r j) = inverseVariance r - (r i - 1) ^ 2 / r i := by
    have h := Finset.sum_erase_add (s := Finset.univ) (f := fun j => (r j - 1) ^ 2 / r j) (Finset.mem_univ i)
    change _ + _ = inverseVariance r at h
    dsimp [S]
    linarith
  have hcs := Finset.sq_sum_div_le_sum_sq_div S (fun j => r j - 1) (fun j _ => hr j)
  rw [hsumD, hsumS, hsumV] at hcs
  have hclear := (div_le_iff₀ hrempos).mp hcs
  have hmul := mul_le_mul_of_nonneg_right hclear (hr i).le
  have hc : ((r i - 1) ^ 2 / r i) * r i = (r i - 1) ^ 2 := div_mul_cancel₀ _ (hr i).ne'
  nlinarith

/-- A fixed rational lower ratio is valid throughout the physical deficit interval.
It is slightly weaker than (1−gamma5)^2, and is the exact endpoint value used
in the source's three bootstrap comparisons. -/
noncomputable def fiveRatioFloor : ℝ := 601000 / 650653

/-- Both stationary coefficients lie in [1−gamma5,1/(1−gamma5)]. -/
theorem five_contender_stationary_coefficient_bounds (A : Board 5 5)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 5)
    (hcont : 2 - dittertConstant 5 ≤ dittertFunctional A) :
    (601 / 625 ≤ dittertAlpha A ∧ dittertAlpha A ≤ 625 / 601) ∧
      (601 / 625 ≤ dittertBeta A ∧ dittertBeta A ≤ 625 / 601) := by
  obtain ⟨hRpos, hCpos⟩ := dittert_contender_products_pos (by norm_num) A hA hmass hcont
  obtain ⟨hρ, hσ, hbudget, hd0, hdg⟩ := dittert_contender_deficit_budget (by norm_num) A hA hmass hcont
  have hRle := rowProduct_le_one (by norm_num) A hA hmass
  have hCle := colProduct_le_one (by norm_num) A hA hmass
  have hp := permanent_nonneg hA
  have hg : dittertConstant 5 = 24 / 625 := by norm_num [dittertConstant, Nat.factorial]
  rw [hg] at hcont hdg
  have hRlo : (601 / 625 : ℝ) ≤ ∏ i, rowSum A i := by linarith
  have hClo : (601 / 625 : ℝ) ≤ ∏ j, colSum A j := by linarith
  unfold dittertFunctional at hcont
  constructor
  · constructor
    · rw [dittertAlpha, le_div_iff₀ hCpos]; nlinarith
    · rw [dittertAlpha, div_le_iff₀ hCpos]; nlinarith
  · constructor
    · rw [dittertBeta, le_div_iff₀ hRpos]; nlinarith
    · rw [dittertBeta, div_le_iff₀ hRpos]; nlinarith

/-- The exact coupling shares the combined inverse-variance bound between axes. -/
theorem five_globalMax_inverseVariance_axis (A : Board 5 5)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 5)
    (hmax : ∀ B : Board 5 5, (∀ i j, 0 ≤ B i j) → totalMass B = 5 →
      dittertFunctional B ≤ dittertFunctional A) :
    (1 + fiveRatioFloor) * inverseVariance (rowSum A) ≤
      inverseVariance (rowSum A) + inverseVariance (colSum A) ∧
    (1 + fiveRatioFloor) * inverseVariance (colSum A) ≤
      inverseVariance (rowSum A) + inverseVariance (colSum A) := by
  have hcont := dittert_globalMax_isContender (by norm_num) A hmax
  obtain ⟨ha, hb⟩ := five_contender_stationary_coefficient_bounds A hA hmass hcont
  obtain ⟨hrow, hcol⟩ := dittert_globalMax_stationary_pair (by norm_num) A hA hmass hmax
  have hcoupled := stationary_inverseVariance_coupled A (dittertAlpha A) (dittertBeta A) hrow hcol
  have hVr := inverseVariance_nonneg (rowSum A) (rowSum_nonneg hA)
  have hVc := inverseVariance_nonneg (colSum A) (colSum_nonneg hA)
  have hL : 0 ≤ fiveRatioFloor := by norm_num [fiveRatioFloor]
  have hLa : fiveRatioFloor * dittertBeta A ≤ dittertAlpha A := by
    have h := mul_le_mul_of_nonneg_left hb.2 hL
    norm_num [fiveRatioFloor] at h ⊢
    linarith [ha.1]
  have hLb : fiveRatioFloor * dittertAlpha A ≤ dittertBeta A := by
    have h := mul_le_mul_of_nonneg_left ha.2 hL
    norm_num [fiveRatioFloor] at h ⊢
    linarith [hb.1]
  have hα : 0 < dittertAlpha A := by linarith [ha.1]
  have hβ : 0 < dittertBeta A := by linarith [hb.1]
  constructor
  · have h := mul_le_mul_of_nonneg_right hLa hVr
    have hh : dittertBeta A * (fiveRatioFloor * inverseVariance (rowSum A)) ≤
        dittertBeta A * inverseVariance (colSum A) := by nlinarith
    have hcancel : fiveRatioFloor * inverseVariance (rowSum A) ≤ inverseVariance (colSum A) := (mul_le_mul_iff_right₀ hβ).mp (by simpa only [mul_comm] using hh)
    linarith
  · have h := mul_le_mul_of_nonneg_right hLb hVc
    have hh : dittertAlpha A * (fiveRatioFloor * inverseVariance (colSum A)) ≤
        dittertAlpha A * inverseVariance (rowSum A) := by nlinarith
    have hcancel : fiveRatioFloor * inverseVariance (colSum A) ≤ inverseVariance (rowSum A) := (mul_le_mul_iff_right₀ hα).mp (by simpa only [mul_comm] using hh)
    linarith

/-- The scalar weighted-coordinate bootstrap, with every rational comparison explicit. -/
theorem five_coordinate_bootstrap {x V t K H a b : ℝ}
    (_hx : 0 < x) (hV0 : 0 ≤ V) (ht : 0 ≤ t) (hK : 0 < K)
    (hH : x ≤ H) (hHcap : H ≤ 5 / 2) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hV : V ≤ (2 / (5 * K)) * t ^ 2)
    (hcoord : (x - 1) ^ 2 ≤ x * (5 - x) * V / 5)
    (hneg : 8 / (25 * K) ≤ a ^ 2)
    (hpos : 2 * H * (5 - H) / (25 * K) ≤ b ^ 2) :
    1 - a * t ≤ x ∧ x ≤ 1 + b * t := by
  constructor
  · by_cases hx1 : 1 ≤ x
    · nlinarith [mul_nonneg ha ht]
    · have hfactor : x * (5 - x) ≤ 4 := by
        nlinarith [mul_nonneg (show 0 ≤ 1 - x by linarith) (show 0 ≤ 4 - x by linarith)]
      have hs : (x - 1) ^ 2 ≤ a ^ 2 * t ^ 2 := by
        calc
          _ ≤ 4 * V / 5 := hcoord.trans (by nlinarith [mul_le_mul_of_nonneg_right hfactor hV0])
          _ ≤ (8 / (25 * K)) * t ^ 2 := by
            have h := mul_le_mul_of_nonneg_left hV (by norm_num : (0 : ℝ) ≤ 4 / 5)
            convert h using 1
            all_goals first | rfl | (field_simp; ring) | ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hneg (sq_nonneg t)
      nlinarith [mul_nonneg ha ht]
  · by_cases hx1 : x ≤ 1
    · nlinarith [mul_nonneg hb ht]
    · have hfactor : x * (5 - x) ≤ H * (5 - H) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hH) (show 0 ≤ 5 - H - x by linarith)]
      have hHfactor : 0 ≤ H * (5 - H) / 5 :=
        div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
      have hs : (x - 1) ^ 2 ≤ b ^ 2 * t ^ 2 := by
        calc
          _ ≤ H * (5 - H) * V / 5 :=
            hcoord.trans (by nlinarith [mul_le_mul_of_nonneg_right hfactor hV0])
          _ ≤ (2 * H * (5 - H) / (25 * K)) * t ^ 2 := by
            have h := mul_le_mul_of_nonneg_left hV hHfactor
            convert h using 1
            all_goals first | rfl | (field_simp; ring) | ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hpos (sq_nonneg t)
      nlinarith [mul_nonneg hb ht]

/-- One genuine stationary-envelope step, using fixed endpoint constants only
after the previous envelope has been proved. -/
theorem five_globalMax_marginal_bootstrap (A : Board 5 5)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 5)
    (hmax : ∀ B : Board 5 5, (∀ i j, 0 ≤ B i j) → totalMass B = 5 →
      dittertFunctional B ≤ dittertFunctional A)
    (a b anew bnew : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hanew : 0 ≤ anew) (hbnew : 0 ≤ bnew)
    (hm0 : 0 < 1 - a * (9 / 20)) (hHcap : 1 + b * (9 / 20) ≤ 5 / 2)
    (hneg : 8 / (25 * ((1 - a * (9 / 20)) * (1 + fiveRatioFloor))) ≤ anew ^ 2)
    (hpos : 2 * (1 + b * (9 / 20)) * (5 - (1 + b * (9 / 20))) /
      (25 * ((1 - a * (9 / 20)) * (1 + fiveRatioFloor))) ≤ bnew ^ 2)
    (hprev :
      (∀ i, 1 - a * fiveDeficitParameter (dittertConstant 5 - A.permanent) ≤ rowSum A i ∧
        rowSum A i ≤ 1 + b * fiveDeficitParameter (dittertConstant 5 - A.permanent)) ∧
      (∀ j, 1 - a * fiveDeficitParameter (dittertConstant 5 - A.permanent) ≤ colSum A j ∧
        colSum A j ≤ 1 + b * fiveDeficitParameter (dittertConstant 5 - A.permanent))) :
    (∀ i, 1 - anew * fiveDeficitParameter (dittertConstant 5 - A.permanent) ≤ rowSum A i ∧
      rowSum A i ≤ 1 + bnew * fiveDeficitParameter (dittertConstant 5 - A.permanent)) ∧
    (∀ j, 1 - anew * fiveDeficitParameter (dittertConstant 5 - A.permanent) ≤ colSum A j ∧
      colSum A j ≤ 1 + bnew * fiveDeficitParameter (dittertConstant 5 - A.permanent)) := by
  let t := fiveDeficitParameter (dittertConstant 5 - A.permanent)
  let m := 1 - a * (9 / 20)
  let H := 1 + b * (9 / 20)
  let K := m * (1 + fiveRatioFloor)
  have ht : 0 ≤ t := fiveDeficitParameter_nonneg _
  have hcont := dittert_globalMax_isContender (by norm_num) A hmax
  obtain ⟨hr, hc⟩ := dittert_contender_marginals_pos (by norm_num) A hA hmass hcont
  obtain ⟨hρ, hσ, hbudget, hd0, hdg⟩ := dittert_contender_deficit_budget (by norm_num) A hA hmass hcont
  have hd1 := hdg.trans_lt (dittertConstant_lt_one (by norm_num))
  have htcap : t ≤ 9 / 20 := (fiveDeficitParameter_lt_cap hd0 hdg).le
  have hm1 : m ≤ 1 := by dsimp [m]; nlinarith
  have hK : 0 < K := mul_pos hm0 (by norm_num [fiveRatioFloor])
  have hminr (i : Fin 5) : m ≤ rowSum A i := by
    have h := mul_le_mul_of_nonneg_left htcap ha
    have hi := (hprev.1 i).1
    change 1 - a * t ≤ rowSum A i at hi
    dsimp [m]
    linarith
  have hminc (j : Fin 5) : m ≤ colSum A j := by
    have h := mul_le_mul_of_nonneg_left htcap ha
    have hj := (hprev.2 j).1
    change 1 - a * t ≤ colSum A j at hj
    dsimp [m]
    linarith
  have hmaxr (i : Fin 5) : rowSum A i ≤ H := by
    have h := mul_le_mul_of_nonneg_left htcap hb
    have hi := (hprev.1 i).2
    change rowSum A i ≤ 1 + b * t at hi
    dsimp [H]
    linarith
  have hmaxc (j : Fin 5) : colSum A j ≤ H := by
    have h := mul_le_mul_of_nonneg_left htcap hb
    have hj := (hprev.2 j).2
    change colSum A j ≤ 1 + b * t at hj
    dsimp [H]
    linarith
  have hsumc : ∑ j, colSum A j = 5 := by rwa [← totalMass_eq_sum_colSum]
  have htotal := inverseVariance_shared_budget (rowSum A) (colSum A) hr hc hmass hsumc
    (by ring) (by ring) hρ hσ hbudget hd1 hm0 hm1 hminr hminc
  have htsq : t ^ 2 = 5 * (dittertConstant 5 - A.permanent) /
      (1 - (dittertConstant 5 - A.permanent)) := fiveDeficitParameter_sq hd0 hd1
  have htotal' : m / 2 * (inverseVariance (rowSum A) + inverseVariance (colSum A)) ≤ t ^ 2 / 5 := by
    rw [htsq]
    convert htotal using 1; ring
  obtain ⟨hVr, hVc⟩ := five_globalMax_inverseVariance_axis A hA hmass hmax
  have haxis {V : ℝ} (hV : (1 + fiveRatioFloor) * V ≤
      inverseVariance (rowSum A) + inverseVariance (colSum A)) : V ≤ (2 / (5 * K)) * t ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hV (by positivity : 0 ≤ m / 2)
    have hh : (K / 2) * V ≤ t ^ 2 / 5 := by dsimp [K]; nlinarith
    have hdiv : V ≤ (t ^ 2 / 5) / (K / 2) :=
      (le_div_iff₀ (by positivity : 0 < K / 2)).mpr (by nlinarith [hh])
    convert hdiv using 1; field_simp
  constructor
  · intro i
    exact five_coordinate_bootstrap (hr i) (inverseVariance_nonneg _ (rowSum_nonneg hA)) ht hK
      (hmaxr i) hHcap hanew hbnew (haxis hVr)
      (five_coordinate_inverseVariance_bound _ hr hmass i) hneg hpos
  · intro j
    exact five_coordinate_bootstrap (hc j) (inverseVariance_nonneg _ (colSum_nonneg hA)) ht hK
      (hmaxc j) hHcap hanew hbnew (haxis hVc)
      (five_coordinate_inverseVariance_bound _ hc hsumc j) hneg hpos

/-- The generic entropy estimate initializes the rational 71/100 envelope. -/
theorem five_initial_marginal_envelope (r : Fin 5 → ℝ)
    (hr : ∀ i, 0 < r i) (hsum : ∑ i, r i = 5) {rho delta : ℝ}
    (hprod : ∏ i, r i = 1 - rho) (hρ : 0 ≤ rho) (hρδ : rho ≤ delta) (hδ : delta < 1) :
    ∀ i, 1 - (71 / 100) * fiveDeficitParameter delta ≤ r i ∧
      r i ≤ 1 + (71 / 100) * fiveDeficitParameter delta := by
  have hd0 : 0 ≤ delta := hρ.trans hρδ
  have ht := fiveDeficitParameter_nonneg delta
  have htsq := fiveDeficitParameter_sq hd0 hδ
  intro i
  have h := subset_discrepancy_sq_le (by norm_num) r hr hsum hprod hρ hρδ hδ {i}
  simp only [Finset.sum_singleton, Finset.card_singleton, Nat.cast_one, Nat.cast_ofNat] at h
  have hcap := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hρδ (by norm_num : (0 : ℝ) ≤ 5))
    (by linarith : 0 ≤ 2 * (1 - delta))
  have heq : 5 * delta / (2 * (1 - delta)) = fiveDeficitParameter delta ^ 2 / 2 := by rw [htsq]; field_simp
  rw [heq] at hcap
  have hs : (r i - 1) ^ 2 ≤ ((71 / 100) * fiveDeficitParameter delta) ^ 2 := by
    nlinarith [sq_nonneg (fiveDeficitParameter delta)]
  have habs : |r i - 1| ≤ (71 / 100) * fiveDeficitParameter delta :=
    (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp (by simpa using hs)
  obtain ⟨hl, hu⟩ := abs_le.mp habs
  constructor <;> linarith

/-- The three original exact comparisons, with no circular envelope hypothesis.
All cell zeros and the zero-deficit endpoint are retained. -/
theorem five_globalMax_marginal_bounds (A : Board 5 5)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 5)
    (hmax : ∀ B : Board 5 5, (∀ i j, 0 ≤ B i j) → totalMass B = 5 →
      dittertFunctional B ≤ dittertFunctional A) :
    (∀ i, 1 - (23 / 50) * fiveDeficitParameter (dittertConstant 5 - A.permanent) ≤ rowSum A i ∧
      rowSum A i ≤ 1 + fiveDeficitParameter (dittertConstant 5 - A.permanent) / 2) ∧
    (∀ j, 1 - (23 / 50) * fiveDeficitParameter (dittertConstant 5 - A.permanent) ≤ colSum A j ∧
      colSum A j ≤ 1 + fiveDeficitParameter (dittertConstant 5 - A.permanent) / 2) := by
  have hcont := dittert_globalMax_isContender (by norm_num) A hmax
  obtain ⟨hr, hc⟩ := dittert_contender_marginals_pos (by norm_num) A hA hmass hcont
  obtain ⟨hρ, hσ, hbudget, hd0, hdg⟩ := dittert_contender_deficit_budget (by norm_num) A hA hmass hcont
  have hd1 := hdg.trans_lt (dittertConstant_lt_one (by norm_num))
  have hr0 := five_initial_marginal_envelope (rowSum A) hr hmass (by ring) hρ
    (by linarith : 1 - (∏ i, rowSum A i) ≤ dittertConstant 5 - A.permanent) hd1
  have hc0 := five_initial_marginal_envelope (colSum A) hc (by rwa [← totalMass_eq_sum_colSum])
    (by ring) hσ (by linarith : 1 - (∏ j, colSum A j) ≤ dittertConstant 5 - A.permanent) hd1
  have h1 := five_globalMax_marginal_bootstrap A hA hmass hmax
    (71 / 100) (71 / 100) (1 / 2) (11 / 20)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [fiveRatioFloor]) (by norm_num [fiveRatioFloor]) ⟨hr0, hc0⟩
  have h2 := five_globalMax_marginal_bootstrap A hA hmass hmax
    (1 / 2) (11 / 20) (47 / 100) (51 / 100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [fiveRatioFloor]) (by norm_num [fiveRatioFloor]) h1
  have h3 := five_globalMax_marginal_bootstrap A hA hmass hmax
    (47 / 100) (51 / 100) (23 / 50) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [fiveRatioFloor]) (by norm_num [fiveRatioFloor]) h2
  simpa only [one_div, inv_mul_eq_div] using h3

end DittertRybin
