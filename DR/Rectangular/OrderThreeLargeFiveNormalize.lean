import DR.Rectangular.OrderThreeLargeFiveReduction
import DR.Rectangular.OrderThreeLargeFiveScalar

/-! Normalization of the retained row direction, including its zero-energy boundary. -/

namespace DittertRybin

theorem orderThree_five_normalized_bound {n E u : ℝ} (hn : 3 ≤ n) (hE : 0 < E)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hsize : 5 * n * E ≤ 2) :
    E * orderThreeFiveExpression n u ≤
      (9 / 5 - 22 / (5 * n)) * E + (18 / 5) * ((n * E * u ^ 2) / n) -
      6 * Real.sqrt ((4 / 5) * (n * E * u ^ 2)) * E -
      9 * (Real.sqrt ((E - (n * E * u ^ 2) / n) * (n * E * u ^ 2)) + E) ^ 2 /
        (6 * (5 * n)⁻¹ * (n - 2)) := by
  have hn0 : 0 < n := by linarith
  have hnne := ne_of_gt hn0
  have hrootn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hrootne := ne_of_gt hrootn
  have hrootSq := Real.sq_sqrt hn0.le
  have huVar : 0 ≤ 1 - u ^ 2 := by nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu1)]
  have hvroot := Real.sqrt_nonneg (1 - u ^ 2)
  have hvSq := Real.sq_sqrt huVar
  let V := u * Real.sqrt (1 - u ^ 2)
  let D := 6 * (5 * n)⁻¹ * (n - 2)
  let T := 3 / (1 - 2 / n)
  have hV : 0 ≤ V := mul_nonneg hu0 hvroot
  have hnsub : 0 < n - 2 := by linarith
  have hD : 0 < D := by dsimp [D]; positivity
  have hDne := ne_of_gt hD
  have hden : 0 < 1 - 2 / n := by
    have heq : 1 - 2 / n = (n - 2) / n := by field_simp
    rw [heq]
    exact div_pos (by linarith) hn0
  have hdenne := ne_of_gt hden
  have hrowdiv : n * E * u ^ 2 / n = E * u ^ 2 := by field_simp
  have hres : 0 ≤ E - n * E * u ^ 2 / n := by
    rw [hrowdiv]
    nlinarith [mul_nonneg hE.le huVar]
  have harg : 0 ≤ (E - n * E * u ^ 2 / n) * (n * E * u ^ 2) := by positivity
  have hR : Real.sqrt ((E - n * E * u ^ 2 / n) * (n * E * u ^ 2)) =
      Real.sqrt n * E * u * Real.sqrt (1 - u ^ 2) := by
    apply (Real.sqrt_eq_iff_eq_sq harg (by positivity)).mpr
    simp only [mul_pow, hrootSq, hvSq]
    rw [hrowdiv]
    ring
  have hRsum : Real.sqrt ((E - n * E * u ^ 2 / n) * (n * E * u ^ 2)) + E =
      E * (Real.sqrt n * V + 1) := by
    rw [hR]
    dsimp [V]
    ring
  have hrowroot : Real.sqrt ((4 / 5) * (n * E * u ^ 2)) ≤ (Real.sqrt 8 / 5) * u := by
    apply le_of_sq_le_sq _ (by positivity)
    rw [Real.sq_sqrt (by positivity : 0 ≤ (4 / 5) * (n * E * u ^ 2)), mul_pow,
      div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
    have h := mul_le_mul_of_nonneg_right hsize (sq_nonneg u)
    nlinarith
  have hrowScaled : 6 * Real.sqrt ((4 / 5) * (n * E * u ^ 2)) * E ≤
      (6 * Real.sqrt 8 / 5) * u * E := by
    have h := mul_le_mul_of_nonneg_right hrowroot (show 0 ≤ 6 * E by positivity)
    nlinarith
  have hEcap : E ≤ 2 / (5 * n) := (le_div_iff₀ (by positivity)).mpr (by nlinarith)
  have hscaled := mul_le_mul_of_nonneg_left hEcap
    (show 0 ≤ 9 / D * E * (Real.sqrt n * V + 1) ^ 2 by positivity)
  have hrootdiv : Real.sqrt n / n = 1 / Real.sqrt n := by
    apply (div_eq_div_iff hnne hrootne).mpr
    nlinarith
  have hnorm : (Real.sqrt n * V + 1) ^ 2 / n = V ^ 2 + 2 * V / Real.sqrt n + 1 / n := by
    calc
      (Real.sqrt n * V + 1) ^ 2 / n = (Real.sqrt n ^ 2 / n) * V ^ 2 +
          2 * (Real.sqrt n / n) * V + 1 / n := by ring
      _ = _ := by rw [hrootSq, div_self hnne, hrootdiv]; ring
  have hscaleid : (9 / D * E * (Real.sqrt n * V + 1) ^ 2) * (2 / (5 * n)) =
      T * E * ((Real.sqrt n * V + 1) ^ 2 / n) := by
    dsimp [D, T]
    field_simp
    ring
  have hcol : 9 * (Real.sqrt ((E - n * E * u ^ 2 / n) * (n * E * u ^ 2)) + E) ^ 2 / D ≤
      T * E * (u ^ 2 * (1 - u ^ 2) + 2 * u * Real.sqrt (1 - u ^ 2) / Real.sqrt n + 1 / n) := by
    calc
      _ = (9 / D * E * (Real.sqrt n * V + 1) ^ 2) * E := by rw [hRsum]; ring
      _ ≤ (9 / D * E * (Real.sqrt n * V + 1) ^ 2) * (2 / (5 * n)) := hscaled
      _ = T * E * (V ^ 2 + 2 * V / Real.sqrt n + 1 / n) := by rw [hscaleid, hnorm]
      _ = _ := by dsimp [V]; rw [mul_pow, hvSq]; ring
  rw [hrowdiv]
  change E * orderThreeFiveExpression n u ≤
    (9 / 5 - 22 / (5 * n)) * E + 18 / 5 * (E * u ^ 2) -
      6 * Real.sqrt (4 / 5 * (n * E * u ^ 2)) * E -
      9 * (Real.sqrt ((E - E * u ^ 2) * (n * E * u ^ 2)) + E) ^ 2 / D
  rw [hrowdiv] at hcol
  dsimp [orderThreeFiveExpression, T] at *
  nlinarith

end DittertRybin
