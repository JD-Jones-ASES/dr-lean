import DR.Certificates.SpectralFiveTwoBlocks

/-! Literal rational consequences of the order-five two-block certificates. -/

namespace DittertRybin.Certificates.SpectralFiveTwoBlocks
open scoped BigOperators
noncomputable section

def smallBlockDenominator (u v : ℝ) : ℝ := (1 + u / 3) ^ 3 * (1 - v / 3) ^ 4
def largeBlockDenominator (u v : ℝ) : ℝ := (1 - u / 2) ^ 3 * (1 + v / 2) ^ 2

def smallBlockNumerator (u v : ℝ) : ℝ :=
  (1 - ((13 / 50 - u - v) / 2) / (79 / 100)) * (1 - v / 3) ^ 4 +
    (1 - v / 3 - (13 / 50 + u + v) / 2) * (1 + u / 3) ^ 3 -
    (3 / 2) * (1 + (v - u - 13 / 50) / 4) ^ 2 * smallBlockDenominator u v

def largeBlockNumerator (u v : ℝ) : ℝ :=
  (1 - u / 2 - (13 / 50 + u + v) / 2) * (1 + v / 2) ^ 2 +
    (1 - ((13 / 50 - u - v) / 2) / (79 / 100)) * (1 - u / 2) ^ 3 -
    (16 / 9) * (1 + (u - v - 13 / 50) / 6) ^ 3 * largeBlockDenominator u v

/-- The literal size-two lower bound at the common crossing cap. -/
def smallBlockFloor (u v : ℝ) : ℝ :=
  (1 - ((13 / 50 - u - v) / 2) / (79 / 100)) / (1 + u / 3) ^ 3 +
    (1 - v / 3 - (13 / 50 + u + v) / 2) / (1 - v / 3) ^ 4 -
    (3 / 2) * (1 + (v - u - 13 / 50) / 4) ^ 2

/-- The literal complementary size-three lower bound at the same crossing cap. -/
def largeBlockFloor (u v : ℝ) : ℝ :=
  (1 - u / 2 - (13 / 50 + u + v) / 2) / (1 - u / 2) ^ 3 +
    (1 - ((13 / 50 - u - v) / 2) / (79 / 100)) / (1 + v / 2) ^ 2 -
    (16 / 9) * (1 + (u - v - 13 / 50) / 6) ^ 3

theorem triangle_unit_coordinates {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (huv : u + v ≤ 13 / 50) :
    ∃ x y : ℝ, (0 ≤ x ∧ x ≤ 1) ∧ (0 ≤ y ∧ y ≤ 1) ∧
      u = (13 / 50) * x ∧ v = (13 / 50) * (1 - x) * y := by
  by_cases heq : u = 13 / 50
  · have hv0 : v = 0 := by linarith
    exact ⟨1, 0, by norm_num, by norm_num, by linarith, by simp [hv0]⟩
  · have hult : u < 13 / 50 := lt_of_le_of_ne (by linarith) heq
    have hd : 0 < 13 / 50 - u := by linarith
    refine ⟨u / (13 / 50), v / (13 / 50 - u), ⟨by positivity, ?_⟩,
      ⟨by positivity, ?_⟩, ?_, ?_⟩
    · apply (div_le_one (by norm_num)).mpr; linarith
    · apply (div_le_one hd).mpr; linarith
    · ring
    · have hcancel := div_mul_cancel₀ v hd.ne'
      calc
        v = (13 / 50 - u) * (v / (13 / 50 - u)) := by nlinarith [hcancel]
        _ = _ := by ring

theorem block_denominators_pos {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (huv : u + v ≤ 13 / 50) :
    0 < smallBlockDenominator u v ∧ 0 < largeBlockDenominator u v := by
  have hr : 0 < 1 + u / 3 := by linarith
  have hs : 0 < 1 - v / 3 := by linarith
  have ha : 0 < 1 - u / 2 := by linarith
  have hb : 0 < 1 + v / 2 := by linarith
  constructor <;> dsimp [smallBlockDenominator, largeBlockDenominator] <;> positivity

theorem smallBlockNumerator_eq {u v : ℝ} (hu : 0 ≤ u) (_hv : 0 ≤ v)
    (huv : u + v ≤ 13 / 50) :
    smallBlockNumerator u v = smallBlockDenominator u v * smallBlockFloor u v := by
  have hr : 1 + u / 3 ≠ 0 := by linarith
  have hs : 1 - v / 3 ≠ 0 := by linarith
  unfold smallBlockNumerator smallBlockDenominator smallBlockFloor
  generalize 1 + u / 3 = r at *
  generalize 1 - v / 3 = s at *
  field_simp [hr, hs]

theorem largeBlockNumerator_eq {u v : ℝ} (_hu : 0 ≤ u) (hv : 0 ≤ v)
    (huv : u + v ≤ 13 / 50) :
    largeBlockNumerator u v = largeBlockDenominator u v * largeBlockFloor u v := by
  have ha : 1 - u / 2 ≠ 0 := by linarith
  have hb : 1 + v / 2 ≠ 0 := by linarith
  unfold largeBlockNumerator largeBlockDenominator largeBlockFloor
  generalize 1 - u / 2 = a at *
  generalize 1 + v / 2 = b at *
  field_simp [ha, hb]

theorem eval_dx (x y : ℝ) : rationalEval ![x,y] dxPolynomial =
    smallBlockDenominator ((13 / 50) * x) ((13 / 50) * (1 - x) * y) := by
  norm_num [rationalEval, uPolynomial, vPolynomial, ePolynomial, fPolynomial, rPolynomial, sPolynomial, aPolynomial, bPolynomial, mTwoPolynomial, mThreePolynomial, dxPolynomial, dyPolynomial, nxPolynomial, nyPolynomial, smallBlockDenominator, largeBlockDenominator,
    smallBlockNumerator, largeBlockNumerator]
  ring

theorem eval_dy (x y : ℝ) : rationalEval ![x,y] dyPolynomial =
    largeBlockDenominator ((13 / 50) * x) ((13 / 50) * (1 - x) * y) := by
  norm_num [rationalEval, uPolynomial, vPolynomial, ePolynomial, fPolynomial, rPolynomial, sPolynomial, aPolynomial, bPolynomial, mTwoPolynomial, mThreePolynomial, dxPolynomial, dyPolynomial, nxPolynomial, nyPolynomial, smallBlockDenominator, largeBlockDenominator,
    smallBlockNumerator, largeBlockNumerator]
  ring

theorem eval_nx (x y : ℝ) : rationalEval ![x,y] nxPolynomial =
    smallBlockNumerator ((13 / 50) * x) ((13 / 50) * (1 - x) * y) := by
  norm_num [rationalEval, uPolynomial, vPolynomial, ePolynomial, fPolynomial, rPolynomial, sPolynomial, aPolynomial, bPolynomial, mTwoPolynomial, mThreePolynomial, dxPolynomial, dyPolynomial, nxPolynomial, nyPolynomial, smallBlockDenominator, largeBlockDenominator,
    smallBlockNumerator, largeBlockNumerator]
  ring

theorem eval_ny (x y : ℝ) : rationalEval ![x,y] nyPolynomial =
    largeBlockNumerator ((13 / 50) * x) ((13 / 50) * (1 - x) * y) := by
  norm_num [rationalEval, uPolynomial, vPolynomial, ePolynomial, fPolynomial, rPolynomial, sPolynomial, aPolynomial, bPolynomial, mTwoPolynomial, mThreePolynomial, dxPolynomial, dyPolynomial, nxPolynomial, nyPolynomial, smallBlockDenominator, largeBlockDenominator,
    smallBlockNumerator, largeBlockNumerator]
  ring

/-- All four literal rational inequalities hold throughout the complete triangle. -/
theorem two_block_scalar_conditions {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (huv : u + v ≤ 13 / 50) :
    24 / 625 < smallBlockFloor u v ∧ 24 / 625 < largeBlockFloor u v ∧
      smallBlockFloor u v + largeBlockFloor u v < 1 ∧
      24 / 625 < smallBlockFloor u v * largeBlockFloor u v := by
  obtain ⟨x, y, hx, hy, huEq, hvEq⟩ := triangle_unit_coordinates hu hv huv
  have hX := xAbove_polynomial_pos x y hx.1 hx.2 hy.1 hy.2
  have hY := yAbove_polynomial_pos x y hx.1 hx.2 hy.1 hy.2
  have hS := sumBelow_polynomial_pos x y hx.1 hx.2 hy.1 hy.2
  have hP := productAbove_polynomial_pos x y hx.1 hx.2 hy.1 hy.2
  have ex : rationalEval ![x,y] xAbovePolynomial = rationalEval ![x,y] nxPolynomial -
      (24 / 625) * rationalEval ![x,y] dxPolynomial := by simp [rationalEval, xAbovePolynomial]
  have ey : rationalEval ![x,y] yAbovePolynomial = rationalEval ![x,y] nyPolynomial -
      (24 / 625) * rationalEval ![x,y] dyPolynomial := by simp [rationalEval, yAbovePolynomial]
  have es : rationalEval ![x,y] sumBelowPolynomial = rationalEval ![x,y] dxPolynomial * rationalEval ![x,y] dyPolynomial -
      rationalEval ![x,y] nxPolynomial * rationalEval ![x,y] dyPolynomial -
      rationalEval ![x,y] nyPolynomial * rationalEval ![x,y] dxPolynomial := by simp [rationalEval, sumBelowPolynomial]
  have ep : rationalEval ![x,y] productAbovePolynomial = rationalEval ![x,y] nxPolynomial * rationalEval ![x,y] nyPolynomial -
      (24 / 625) * rationalEval ![x,y] dxPolynomial * rationalEval ![x,y] dyPolynomial := by simp [rationalEval, productAbovePolynomial]
  rw [ex, eval_nx, eval_dx, ← huEq, ← hvEq] at hX
  rw [ey, eval_ny, eval_dy, ← huEq, ← hvEq] at hY
  rw [es, eval_dx, eval_dy, eval_nx, eval_ny, ← huEq, ← hvEq] at hS
  rw [ep, eval_dx, eval_dy, eval_nx, eval_ny, ← huEq, ← hvEq] at hP
  obtain ⟨hDX, hDY⟩ := block_denominators_pos hu hv huv
  rw [smallBlockNumerator_eq hu hv huv] at hX hS hP
  rw [largeBlockNumerator_eq hu hv huv] at hY hS hP
  have hX' : 24 / 625 < smallBlockFloor u v := by nlinarith
  have hY' : 24 / 625 < largeBlockFloor u v := by nlinarith
  have hDXY := mul_pos hDX hDY
  refine ⟨hX', hY', ?_, ?_⟩
  · nlinarith
  · nlinarith


/-- The two positive literal permanent floors exceed the actual permanent deficit. -/
theorem two_block_floor_gap {u v delta : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (huv : u + v ≤ 13 / 50) (hd0 : 0 ≤ delta) (hdg : delta ≤ 24 / 625) :
    0 < smallBlockFloor u v - delta ∧ 0 < largeBlockFloor u v - delta ∧
      24 / 625 - delta < (smallBlockFloor u v - delta) * (largeBlockFloor u v - delta) := by
  obtain ⟨hX, hY, hS, hP⟩ := two_block_scalar_conditions hu hv huv
  have hb := mul_nonneg hd0 (show 0 ≤ 1 - smallBlockFloor u v - largeBlockFloor u v by linarith)
  refine ⟨by linarith, by linarith, ?_⟩
  nlinarith [sq_nonneg delta]

end
end DittertRybin.Certificates.SpectralFiveTwoBlocks
