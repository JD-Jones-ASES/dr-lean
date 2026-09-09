import DR.Certificates.BernsteinTensorTwo
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Tactic.FinCases

/-!
# The order-five singleton derivative certificate

Thirty exact tensor Bernstein coefficients prove the polynomial controlling
the crossing derivative is positive on the complete marginal rectangle.
This is Appendix B of Analytic-Lab P0174 `SQUARE_ENDPOINT_5.md`.
-/

namespace DittertRybin.Certificates.SpectralFiveDerivative
open scoped BigOperators
open MvPolynomial
noncomputable section

def derivativePolynomial : MvPolynomial (Fin 2) ℚ :=
  X 0 + X 1 - C (61 / 16384) * X 0 ^ 2 * X 1 * (10 - X 0 - X 1) ^ 3

def coefficients : Fin 6 → Fin 5 → ℚ :=
  ![![(8171940050141371773 : ℚ) / 16384000000000000000, (1333885640959597076637 : ℚ) / 2621440000000000000000, (342362478719180576661 : ℚ) / 655360000000000000000, (353447597380392324519 : ℚ) / 655360000000000000000, (45828436079771530869 : ℚ) / 81920000000000000000], ![(17392723250471529 : ℚ) / 40960000000000000, (5645256553677176049 : ℚ) / 13107200000000000000, (115501769589960328101 : ℚ) / 262144000000000000000, (59528983392653854719 : ℚ) / 131072000000000000000, (15441260290677034527 : ℚ) / 32768000000000000000], ![(11354943067833 : ℚ) / 32768000000000, (9135674132849979 : ℚ) / 26214400000000000, (185937292994502279 : ℚ) / 524288000000000000, (15300090287893852359 : ℚ) / 41943040000000000000, (1985594223556553727 : ℚ) / 5242880000000000000], ![(5427426009 : ℚ) / 20480000000, (6889086226167 : ℚ) / 26214400000000, (138997178216823 : ℚ) / 524288000000000, (11398400364456843 : ℚ) / 41943040000000000, (118500749540984949 : ℚ) / 419430400000000000], ![(231159 : ℚ) / 1280000, (142644693 : ℚ) / 819200000, (45235509981 : ℚ) / 262144000000, (3684000912609 : ℚ) / 20971520000000, (19213249540533 : ℚ) / 104857600000000], ![(3 : ℚ) / 32, (3399 : ℚ) / 40960, (507867 : ℚ) / 6553600, (323125053 : ℚ) / 4194304000, (3413453541 : ℚ) / 41943040000]]
def margin : ℚ := (323125053 : ℚ) / 4194304000

theorem coefficient_identity :
    affineNormalize ![(793 : ℚ) / 1000, (1 : ℚ) / 1] ![(1 : ℚ) / 1, (49 : ℚ) / 40] derivativePolynomial =
      tensorPolynomial ![5, 4] (fun a => coefficients (a 0) (a 1)) := by
  apply MvPolynomial.funext
  intro z
  rw [tensorPolynomial_two]
  norm_num [affineNormalize, derivativePolynomial, coefficients, Fin.sum_univ_succ,
    Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  dsimp
  ring

theorem coefficients_ge_margin (a : BernsteinIndex ![5, 4]) :
    margin ≤ coefficients (a 0) (a 1) := by
  generalize a 0 = i
  generalize a 1 = j
  fin_cases i <;> fin_cases j <;> decide +kernel

def certificate : BernsteinCertificate derivativePolynomial
    ![(793 : ℚ) / 1000, (1 : ℚ) / 1] ![(1 : ℚ) / 1, (49 : ℚ) / 40] where
  degree := ![5, 4]
  coefficients := fun a => coefficients (a 0) (a 1)
  margin := margin
  identity := coefficient_identity
  coefficient_bound := coefficients_ge_margin

theorem derivativePolynomial_pos (a b : ℝ)
    (ha : 793 / 1000 ≤ a) (ha1 : a ≤ 1) (hb : 1 ≤ b) (hb1 : b ≤ 49 / 40) :
    0 < a + b - (61 / 16384) * a ^ 2 * b * (10 - a - b) ^ 3 := by
  have h := certificate.pos (by intro i; fin_cases i <;> norm_num)
    (by norm_num [certificate, margin]) ![a, b]
    (by intro i; fin_cases i <;> norm_num <;> exact ⟨by assumption, by assumption⟩)
  simpa [rationalEval, derivativePolynomial] using h


/-- The literal derivative of the singleton minor lower bound is negative
on the full physical marginal and crossing domain. -/
theorem singleton_minor_derivative_neg (a b L w : ℝ)
    (ha : 793 / 1000 ≤ a) (ha1 : a ≤ 1) (hb : 1 ≤ b) (hb1 : b ≤ 49 / 40)
    (hL : 0 < L) (hLa : L ≤ a) (hw : 0 ≤ w) (hw1 : w ≤ 13 / 50) :
    -1 / (2 * a ^ 2) - 1 / (2 * L * b) +
      (61 / 64) * ((10 - a - b - w) / 8) ^ 3 < 0 := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hK := derivativePolynomial_pos a b ha ha1 hb hb1
  have hclear : (2 * a ^ 2 * b) *
      (-1 / (2 * a ^ 2) - 1 / (2 * a * b) + (61 / 64) * ((10 - a - b) / 8) ^ 3) =
        -(a + b - (61 / 16384) * a ^ 2 * b * (10 - a - b) ^ 3) := by
    field_simp [ha0.ne', hb0.ne']
    ring
  have hD : -1 / (2 * a ^ 2) - 1 / (2 * a * b) +
      (61 / 64) * ((10 - a - b) / 8) ^ 3 < 0 := by
    have hh : (2 * a ^ 2 * b) *
        (-1 / (2 * a ^ 2) - 1 / (2 * a * b) + (61 / 64) * ((10 - a - b) / 8) ^ 3) < 0 := by
      rw [hclear]
      linarith
    by_contra! hnon
    exact (not_lt_of_ge (mul_nonneg (by positivity) hnon)) hh
  have hinv : 1 / (2 * a * b) ≤ 1 / (2 * L * b) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hbase0 : 0 ≤ (10 - a - b - w) / 8 := by linarith
  have hbase : (10 - a - b - w) / 8 ≤ (10 - a - b) / 8 := by linarith
  have hpow := pow_le_pow_left₀ hbase0 hbase 3
  linarith

end
end DittertRybin.Certificates.SpectralFiveDerivative
