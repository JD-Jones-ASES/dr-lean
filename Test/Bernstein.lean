import DR.Certificates.SpectralSeven
import DR.Certificates.SpectralEight

/-!
Independent exact rejection controls for the Bernstein certificate contract.
The first mutation preserves the positive coefficient margin and breaks the
polynomial identity. The second preserves the polynomial identity and breaks
the claimed margin. These are proved semantic rejections, not failed numerical
searches or unchecked expected-status strings.
-/

namespace DittertRybin.Certificates.BernsteinTests

open SpectralEight
noncomputable section

def changedCoefficients : Fin 17 → ℚ :=
  fun a ↦ if a = 0 then coefficients a + 1 else coefficients a

theorem changed_coefficients_keep_margin (a : BernsteinIndex (fun _ : Fin 1 ↦ 16)) :
    margin ≤ changedCoefficients (a 0) := by
  have h := coefficients_ge_margin a
  unfold changedCoefficients
  split_ifs <;> linarith

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem changed_coefficient_rejected :
    affineNormalize (fun _ : Fin 1 ↦ 0) (fun _ ↦ 1) gapPolynomial ≠
      tensorPolynomial (fun _ : Fin 1 ↦ 16) (fun a ↦ changedCoefficients (a 0)) := by
  intro h
  have he := congrArg (MvPolynomial.eval (fun _ : Fin 1 ↦ (0 : ℚ))) h
  rw [tensorPolynomial_one] at he
  norm_num [affineNormalize, gapPolynomial, changedCoefficients, coefficients,
    Fin.sum_univ_succ, Nat.choose] at he

theorem inflated_margin_rejected :
    ¬∀ a : BernsteinIndex (fun _ : Fin 1 ↦ 16), margin + 1 ≤ coefficients (a 0) := by
  intro h
  have he := h (fun _ ↦ ⟨6, by norm_num⟩)
  norm_num [margin, coefficients] at he

-- The actual scalar inequalities include both endpoints of the unit interval.
example (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    1 - z ^ 2 < (8 / 7 : ℝ) ^ 7 *
      (1 - (7 / 50 : ℝ) * z - (73 / 1000 : ℝ) * (1 - z ^ 2)) ^ 8 :=
  sub_pos.mp (SpectralEight.gap_pos z hz hz1)

example (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    1 - z ^ 2 < (7 / 6 : ℝ) ^ 6 *
      (1 - (21 / 100 : ℝ) * z - (71 / 1000 : ℝ) * (1 - z ^ 2)) ^ 7 :=
  sub_pos.mp (SpectralSeven.gap_pos z hz hz1)

end
end DittertRybin.Certificates.BernsteinTests
