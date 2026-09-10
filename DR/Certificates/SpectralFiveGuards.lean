import DR.Certificates.Bernstein
import DR.Square.FiveMarginalBounds
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.CharZero.Infinite

/-!
# Exact scalar guards for order five

The 67 rational Bernstein coefficients certify the scalar guards used by
the singleton and two-block permanent comparisons.
Every coefficient table has a proved polynomial identity and positive margin.
-/

namespace DittertRybin.Certificates.SpectralFiveGuards
open scoped BigOperators
open MvPolynomial
noncomputable section

def heightPolynomial : MvPolynomial (Fin 1) ℚ := 1 + C (1 / 2) * X 0
def dominationPolynomial : MvPolynomial (Fin 1) ℚ := 1 - X 0
def energyPolynomial : MvPolynomial (Fin 1) ℚ :=
  heightPolynomial * (C (24 / 625) - C ((1 - 24 / 625) / 5) * X 0 ^ 2)
def denominatorPolynomial : MvPolynomial (Fin 1) ℚ :=
  C (19 / 100) * dominationPolynomial - energyPolynomial
def crossingNumeratorPolynomial : MvPolynomial (Fin 1) ℚ :=
  energyPolynomial * (2 * dominationPolynomial - energyPolynomial)
def crossingPolynomial : MvPolynomial (Fin 1) ℚ :=
  C (13 / 25) * denominatorPolynomial - crossingNumeratorPolynomial

def height (t : ℝ) : ℝ := 1 + t / 2
def domination (t : ℝ) : ℝ := 1 - t
def energy (t : ℝ) : ℝ := height t * ((24 / 625) - ((1 - 24 / 625) / 5) * t ^ 2)
def denominator (t : ℝ) : ℝ := (19 / 100) * domination t - energy t
def crossingNumerator (t : ℝ) : ℝ := energy t * (2 * domination t - energy t)
def crossingBound (t : ℝ) : ℝ := crossingNumerator t / (2 * denominator t)

def denominatorCoefficients : Fin 4 → ℚ := ![(379 : ℚ) / 2500, (6011 : ℚ) / 50000, (127277 : ℚ) / 1250000, (5258369 : ℚ) / 50000000]
def denominatorMargin : ℚ := (127277 : ℚ) / 1250000

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem denominator_coefficient_identity :
    affineNormalize (fun _ : Fin 1 => (0 : ℚ) / 1) (fun _ => (9 : ℚ) / 20) denominatorPolynomial =
      tensorPolynomial (fun _ : Fin 1 => 3) (fun a => denominatorCoefficients (a 0)) := by
  apply MvPolynomial.funext
  intro x
  rw [tensorPolynomial_one]
  norm_num [affineNormalize, heightPolynomial, dominationPolynomial, energyPolynomial,
    denominatorPolynomial, crossingNumeratorPolynomial, crossingPolynomial,
    denominatorCoefficients, Fin.sum_univ_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial, Nat.factorial]
  ring

theorem denominator_coefficients_ge_margin (a : BernsteinIndex (fun _ : Fin 1 => 3)) :
    denominatorMargin ≤ denominatorCoefficients (a 0) := by
  generalize a 0 = b
  fin_cases b <;> norm_num [denominatorCoefficients, denominatorMargin]

def denominatorCertificate : BernsteinCertificate denominatorPolynomial
    (fun _ => (0 : ℚ) / 1) (fun _ => (9 : ℚ) / 20) where
  degree := fun _ => 3
  coefficients := fun a => denominatorCoefficients (a 0)
  margin := denominatorMargin
  identity := denominator_coefficient_identity
  coefficient_bound := denominator_coefficients_ge_margin

theorem denominator_polynomial_pos (t : ℝ) (ht : ((0 : ℚ) / 1 : ℝ) ≤ t)
    (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) : 0 < rationalEval (fun _ : Fin 1 => t) denominatorPolynomial := by
  exact denominatorCertificate.pos (by intro i; norm_num)
    (by norm_num [denominatorCertificate, denominatorMargin]) (fun _ => t)
    (fun _ => by norm_num at *; exact ⟨ht, ht1⟩)

def crossing0Coefficients : Fin 7 → ℚ := ![(5479 : ℚ) / 1562500, (549809 : ℚ) / 187500000, (1789192 : ℚ) / 732421875, (1273227899 : ℚ) / 625000000000, (6696211311 : ℚ) / 3906250000000, (276173898841 : ℚ) / 187500000000000, (3280205202881 : ℚ) / 2500000000000000]
def crossing0Margin : ℚ := (3280205202881 : ℚ) / 2500000000000000

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem crossing0_coefficient_identity :
    affineNormalize (fun _ : Fin 1 => (0 : ℚ) / 1) (fun _ => (1 : ℚ) / 20) crossingPolynomial =
      tensorPolynomial (fun _ : Fin 1 => 6) (fun a => crossing0Coefficients (a 0)) := by
  apply MvPolynomial.funext
  intro x
  rw [tensorPolynomial_one]
  norm_num [affineNormalize, heightPolynomial, dominationPolynomial, energyPolynomial,
    denominatorPolynomial, crossingNumeratorPolynomial, crossingPolynomial,
    crossing0Coefficients, Fin.sum_univ_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial, Nat.factorial]
  ring

theorem crossing0_coefficients_ge_margin (a : BernsteinIndex (fun _ : Fin 1 => 6)) :
    crossing0Margin ≤ crossing0Coefficients (a 0) := by
  generalize a 0 = b
  fin_cases b <;> norm_num [crossing0Coefficients, crossing0Margin]

def crossing0Certificate : BernsteinCertificate crossingPolynomial
    (fun _ => (0 : ℚ) / 1) (fun _ => (1 : ℚ) / 20) where
  degree := fun _ => 6
  coefficients := fun a => crossing0Coefficients (a 0)
  margin := crossing0Margin
  identity := crossing0_coefficient_identity
  coefficient_bound := crossing0_coefficients_ge_margin

theorem crossing0_polynomial_pos (t : ℝ) (ht : ((0 : ℚ) / 1 : ℝ) ≤ t)
    (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) : 0 < rationalEval (fun _ : Fin 1 => t) crossingPolynomial := by
  exact crossing0Certificate.pos (by intro i; norm_num)
    (by norm_num [crossing0Certificate, crossing0Margin]) (fun _ => t)
    (fun _ => by norm_num at *; exact ⟨ht, ht1⟩)

def crossing1Coefficients : Fin 7 → ℚ := ![(3280205202881 : ℚ) / 2500000000000000, (4317137631823 : ℚ) / 3750000000000000, (2007841084283 : ℚ) / 1875000000000000, (334294705841 : ℚ) / 312500000000000, (537507763043 : ℚ) / 468750000000000, (101591560781 : ℚ) / 78125000000000, (59744305641 : ℚ) / 39062500000000]
def crossing1Margin : ℚ := (334294705841 : ℚ) / 312500000000000

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem crossing1_coefficient_identity :
    affineNormalize (fun _ : Fin 1 => (1 : ℚ) / 20) (fun _ => (1 : ℚ) / 10) crossingPolynomial =
      tensorPolynomial (fun _ : Fin 1 => 6) (fun a => crossing1Coefficients (a 0)) := by
  apply MvPolynomial.funext
  intro x
  rw [tensorPolynomial_one]
  norm_num [affineNormalize, heightPolynomial, dominationPolynomial, energyPolynomial,
    denominatorPolynomial, crossingNumeratorPolynomial, crossingPolynomial,
    crossing1Coefficients, Fin.sum_univ_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial, Nat.factorial]
  ring

theorem crossing1_coefficients_ge_margin (a : BernsteinIndex (fun _ : Fin 1 => 6)) :
    crossing1Margin ≤ crossing1Coefficients (a 0) := by
  generalize a 0 = b
  fin_cases b <;> norm_num [crossing1Coefficients, crossing1Margin]

def crossing1Certificate : BernsteinCertificate crossingPolynomial
    (fun _ => (1 : ℚ) / 20) (fun _ => (1 : ℚ) / 10) where
  degree := fun _ => 6
  coefficients := fun a => crossing1Coefficients (a 0)
  margin := crossing1Margin
  identity := crossing1_coefficient_identity
  coefficient_bound := crossing1_coefficients_ge_margin

theorem crossing1_polynomial_pos (t : ℝ) (ht : ((1 : ℚ) / 20 : ℝ) ≤ t)
    (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) : 0 < rationalEval (fun _ : Fin 1 => t) crossingPolynomial := by
  exact crossing1Certificate.pos (by intro i; norm_num)
    (by norm_num [crossing1Certificate, crossing1Margin]) (fun _ => t)
    (fun _ => by norm_num at *; exact ⟨ht, ht1⟩)

def crossing2Coefficients : Fin 7 → ℚ := ![(59744305641 : ℚ) / 39062500000000, (137385661783 : ℚ) / 78125000000000, (967036975067 : ℚ) / 468750000000000, (762976989867 : ℚ) / 312500000000000, (5423748508523 : ℚ) / 1875000000000000, (12806107127789 : ℚ) / 3750000000000000, (10017230576569 : ℚ) / 2500000000000000]
def crossing2Margin : ℚ := (59744305641 : ℚ) / 39062500000000

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem crossing2_coefficient_identity :
    affineNormalize (fun _ : Fin 1 => (1 : ℚ) / 10) (fun _ => (3 : ℚ) / 20) crossingPolynomial =
      tensorPolynomial (fun _ : Fin 1 => 6) (fun a => crossing2Coefficients (a 0)) := by
  apply MvPolynomial.funext
  intro x
  rw [tensorPolynomial_one]
  norm_num [affineNormalize, heightPolynomial, dominationPolynomial, energyPolynomial,
    denominatorPolynomial, crossingNumeratorPolynomial, crossingPolynomial,
    crossing2Coefficients, Fin.sum_univ_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial, Nat.factorial]
  ring

theorem crossing2_coefficients_ge_margin (a : BernsteinIndex (fun _ : Fin 1 => 6)) :
    crossing2Margin ≤ crossing2Coefficients (a 0) := by
  generalize a 0 = b
  fin_cases b <;> norm_num [crossing2Coefficients, crossing2Margin]

def crossing2Certificate : BernsteinCertificate crossingPolynomial
    (fun _ => (1 : ℚ) / 10) (fun _ => (3 : ℚ) / 20) where
  degree := fun _ => 6
  coefficients := fun a => crossing2Coefficients (a 0)
  margin := crossing2Margin
  identity := crossing2_coefficient_identity
  coefficient_bound := crossing2_coefficients_ge_margin

theorem crossing2_polynomial_pos (t : ℝ) (ht : ((1 : ℚ) / 10 : ℝ) ≤ t)
    (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) : 0 < rationalEval (fun _ : Fin 1 => t) crossingPolynomial := by
  exact crossing2Certificate.pos (by intro i; norm_num)
    (by norm_num [crossing2Certificate, crossing2Margin]) (fun _ => t)
    (fun _ => by norm_num at *; exact ⟨ht, ht1⟩)

def crossing3Coefficients : Fin 7 → ℚ := ![(10017230576569 : ℚ) / 2500000000000000, (8622792300959 : ℚ) / 1875000000000000, (2465806495663 : ℚ) / 468750000000000, (467973741859 : ℚ) / 78125000000000, (66272236799 : ℚ) / 9765625000000, (112022460623 : ℚ) / 14648437500000, (5231785571 : ℚ) / 610351562500]
def crossing3Margin : ℚ := (10017230576569 : ℚ) / 2500000000000000

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem crossing3_coefficient_identity :
    affineNormalize (fun _ : Fin 1 => (3 : ℚ) / 20) (fun _ => (1 : ℚ) / 5) crossingPolynomial =
      tensorPolynomial (fun _ : Fin 1 => 6) (fun a => crossing3Coefficients (a 0)) := by
  apply MvPolynomial.funext
  intro x
  rw [tensorPolynomial_one]
  norm_num [affineNormalize, heightPolynomial, dominationPolynomial, energyPolynomial,
    denominatorPolynomial, crossingNumeratorPolynomial, crossingPolynomial,
    crossing3Coefficients, Fin.sum_univ_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial, Nat.factorial]
  ring

theorem crossing3_coefficients_ge_margin (a : BernsteinIndex (fun _ : Fin 1 => 6)) :
    crossing3Margin ≤ crossing3Coefficients (a 0) := by
  generalize a 0 = b
  fin_cases b <;> norm_num [crossing3Coefficients, crossing3Margin]

def crossing3Certificate : BernsteinCertificate crossingPolynomial
    (fun _ => (3 : ℚ) / 20) (fun _ => (1 : ℚ) / 5) where
  degree := fun _ => 6
  coefficients := fun a => crossing3Coefficients (a 0)
  margin := crossing3Margin
  identity := crossing3_coefficient_identity
  coefficient_bound := crossing3_coefficients_ge_margin

theorem crossing3_polynomial_pos (t : ℝ) (ht : ((3 : ℚ) / 20 : ℝ) ≤ t)
    (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) : 0 < rationalEval (fun _ : Fin 1 => t) crossingPolynomial := by
  exact crossing3Certificate.pos (by intro i; norm_num)
    (by norm_num [crossing3Certificate, crossing3Margin]) (fun _ => t)
    (fun _ => by norm_num at *; exact ⟨ht, ht1⟩)

def crossing4Coefficients : Fin 7 → ℚ := ![(5231785571 : ℚ) / 610351562500, (27820649357 : ℚ) / 2929687500000, (61427971009 : ℚ) / 5859375000000, (36040182773 : ℚ) / 3125000000000, (47406920779 : ℚ) / 3750000000000, (2761779687 : ℚ) / 200000000000, (2405152641 : ℚ) / 160000000000]
def crossing4Margin : ℚ := (5231785571 : ℚ) / 610351562500

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem crossing4_coefficient_identity :
    affineNormalize (fun _ : Fin 1 => (1 : ℚ) / 5) (fun _ => (1 : ℚ) / 4) crossingPolynomial =
      tensorPolynomial (fun _ : Fin 1 => 6) (fun a => crossing4Coefficients (a 0)) := by
  apply MvPolynomial.funext
  intro x
  rw [tensorPolynomial_one]
  norm_num [affineNormalize, heightPolynomial, dominationPolynomial, energyPolynomial,
    denominatorPolynomial, crossingNumeratorPolynomial, crossingPolynomial,
    crossing4Coefficients, Fin.sum_univ_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial, Nat.factorial]
  ring

theorem crossing4_coefficients_ge_margin (a : BernsteinIndex (fun _ : Fin 1 => 6)) :
    crossing4Margin ≤ crossing4Coefficients (a 0) := by
  generalize a 0 = b
  fin_cases b <;> norm_num [crossing4Coefficients, crossing4Margin]

def crossing4Certificate : BernsteinCertificate crossingPolynomial
    (fun _ => (1 : ℚ) / 5) (fun _ => (1 : ℚ) / 4) where
  degree := fun _ => 6
  coefficients := fun a => crossing4Coefficients (a 0)
  margin := crossing4Margin
  identity := crossing4_coefficient_identity
  coefficient_bound := crossing4_coefficients_ge_margin

theorem crossing4_polynomial_pos (t : ℝ) (ht : ((1 : ℚ) / 5 : ℝ) ≤ t)
    (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) : 0 < rationalEval (fun _ : Fin 1 => t) crossingPolynomial := by
  exact crossing4Certificate.pos (by intro i; norm_num)
    (by norm_num [crossing4Certificate, crossing4Margin]) (fun _ => t)
    (fun _ => by norm_num at *; exact ⟨ht, ht1⟩)

def crossing5Coefficients : Fin 7 → ℚ := ![(2405152641 : ℚ) / 160000000000, (6502203831 : ℚ) / 400000000000, (263026017391 : ℚ) / 15000000000000, (235863319863 : ℚ) / 12500000000000, (1898966842399 : ℚ) / 93750000000000, (1016855284333 : ℚ) / 46875000000000, (905426937649 : ℚ) / 39062500000000]
def crossing5Margin : ℚ := (2405152641 : ℚ) / 160000000000

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem crossing5_coefficient_identity :
    affineNormalize (fun _ : Fin 1 => (1 : ℚ) / 4) (fun _ => (3 : ℚ) / 10) crossingPolynomial =
      tensorPolynomial (fun _ : Fin 1 => 6) (fun a => crossing5Coefficients (a 0)) := by
  apply MvPolynomial.funext
  intro x
  rw [tensorPolynomial_one]
  norm_num [affineNormalize, heightPolynomial, dominationPolynomial, energyPolynomial,
    denominatorPolynomial, crossingNumeratorPolynomial, crossingPolynomial,
    crossing5Coefficients, Fin.sum_univ_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial, Nat.factorial]
  ring

theorem crossing5_coefficients_ge_margin (a : BernsteinIndex (fun _ : Fin 1 => 6)) :
    crossing5Margin ≤ crossing5Coefficients (a 0) := by
  generalize a 0 = b
  fin_cases b <;> norm_num [crossing5Coefficients, crossing5Margin]

def crossing5Certificate : BernsteinCertificate crossingPolynomial
    (fun _ => (1 : ℚ) / 4) (fun _ => (3 : ℚ) / 10) where
  degree := fun _ => 6
  coefficients := fun a => crossing5Coefficients (a 0)
  margin := crossing5Margin
  identity := crossing5_coefficient_identity
  coefficient_bound := crossing5_coefficients_ge_margin

theorem crossing5_polynomial_pos (t : ℝ) (ht : ((1 : ℚ) / 4 : ℝ) ≤ t)
    (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) : 0 < rationalEval (fun _ : Fin 1 => t) crossingPolynomial := by
  exact crossing5Certificate.pos (by intro i; norm_num)
    (by norm_num [crossing5Certificate, crossing5Margin]) (fun _ => t)
    (fun _ => by norm_num at *; exact ⟨ht, ht1⟩)

def crossing6Coefficients : Fin 7 → ℚ := ![(905426937649 : ℚ) / 39062500000000, (5780846830123 : ℚ) / 234375000000000, (12281115845827 : ℚ) / 468750000000000, (8681655114301 : ℚ) / 312500000000000, (18379825619329 : ℚ) / 625000000000000, (116538672609203 : ℚ) / 3750000000000000, (81967577378609 : ℚ) / 2500000000000000]
def crossing6Margin : ℚ := (905426937649 : ℚ) / 39062500000000

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem crossing6_coefficient_identity :
    affineNormalize (fun _ : Fin 1 => (3 : ℚ) / 10) (fun _ => (7 : ℚ) / 20) crossingPolynomial =
      tensorPolynomial (fun _ : Fin 1 => 6) (fun a => crossing6Coefficients (a 0)) := by
  apply MvPolynomial.funext
  intro x
  rw [tensorPolynomial_one]
  norm_num [affineNormalize, heightPolynomial, dominationPolynomial, energyPolynomial,
    denominatorPolynomial, crossingNumeratorPolynomial, crossingPolynomial,
    crossing6Coefficients, Fin.sum_univ_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial, Nat.factorial]
  ring

theorem crossing6_coefficients_ge_margin (a : BernsteinIndex (fun _ : Fin 1 => 6)) :
    crossing6Margin ≤ crossing6Coefficients (a 0) := by
  generalize a 0 = b
  fin_cases b <;> norm_num [crossing6Coefficients, crossing6Margin]

def crossing6Certificate : BernsteinCertificate crossingPolynomial
    (fun _ => (3 : ℚ) / 10) (fun _ => (7 : ℚ) / 20) where
  degree := fun _ => 6
  coefficients := fun a => crossing6Coefficients (a 0)
  margin := crossing6Margin
  identity := crossing6_coefficient_identity
  coefficient_bound := crossing6_coefficients_ge_margin

theorem crossing6_polynomial_pos (t : ℝ) (ht : ((3 : ℚ) / 10 : ℝ) ≤ t)
    (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) : 0 < rationalEval (fun _ : Fin 1 => t) crossingPolynomial := by
  exact crossing6Certificate.pos (by intro i; norm_num)
    (by norm_num [crossing6Certificate, crossing6Margin]) (fun _ => t)
    (fun _ => by norm_num at *; exact ⟨ht, ht1⟩)

def crossing7Coefficients : Fin 7 → ℚ := ![(81967577378609 : ℚ) / 2500000000000000, (4042626860207 : ℚ) / 117187500000000, (4247803985963 : ℚ) / 117187500000000, (2971681628273 : ℚ) / 78125000000000, (291971208143 : ℚ) / 7324218750000, (203733679993 : ℚ) / 4882812500000, (26622291729 : ℚ) / 610351562500]
def crossing7Margin : ℚ := (81967577378609 : ℚ) / 2500000000000000

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem crossing7_coefficient_identity :
    affineNormalize (fun _ : Fin 1 => (7 : ℚ) / 20) (fun _ => (2 : ℚ) / 5) crossingPolynomial =
      tensorPolynomial (fun _ : Fin 1 => 6) (fun a => crossing7Coefficients (a 0)) := by
  apply MvPolynomial.funext
  intro x
  rw [tensorPolynomial_one]
  norm_num [affineNormalize, heightPolynomial, dominationPolynomial, energyPolynomial,
    denominatorPolynomial, crossingNumeratorPolynomial, crossingPolynomial,
    crossing7Coefficients, Fin.sum_univ_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial, Nat.factorial]
  ring

theorem crossing7_coefficients_ge_margin (a : BernsteinIndex (fun _ : Fin 1 => 6)) :
    crossing7Margin ≤ crossing7Coefficients (a 0) := by
  generalize a 0 = b
  fin_cases b <;> norm_num [crossing7Coefficients, crossing7Margin]

def crossing7Certificate : BernsteinCertificate crossingPolynomial
    (fun _ => (7 : ℚ) / 20) (fun _ => (2 : ℚ) / 5) where
  degree := fun _ => 6
  coefficients := fun a => crossing7Coefficients (a 0)
  margin := crossing7Margin
  identity := crossing7_coefficient_identity
  coefficient_bound := crossing7_coefficients_ge_margin

theorem crossing7_polynomial_pos (t : ℝ) (ht : ((7 : ℚ) / 20 : ℝ) ≤ t)
    (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) : 0 < rationalEval (fun _ : Fin 1 => t) crossingPolynomial := by
  exact crossing7Certificate.pos (by intro i; norm_num)
    (by norm_num [crossing7Certificate, crossing7Margin]) (fun _ => t)
    (fun _ => by norm_num at *; exact ⟨ht, ht1⟩)

def crossing8Coefficients : Fin 7 → ℚ := ![(26622291729 : ℚ) / 610351562500, (222222987671 : ℚ) / 4882812500000, (347439131177 : ℚ) / 7324218750000, (3858835864719 : ℚ) / 78125000000000, (6020782330463 : ℚ) / 117187500000000, (6256356522499 : ℚ) / 117187500000000, (138554002490161 : ℚ) / 2500000000000000]
def crossing8Margin : ℚ := (26622291729 : ℚ) / 610351562500

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem crossing8_coefficient_identity :
    affineNormalize (fun _ : Fin 1 => (2 : ℚ) / 5) (fun _ => (9 : ℚ) / 20) crossingPolynomial =
      tensorPolynomial (fun _ : Fin 1 => 6) (fun a => crossing8Coefficients (a 0)) := by
  apply MvPolynomial.funext
  intro x
  rw [tensorPolynomial_one]
  norm_num [affineNormalize, heightPolynomial, dominationPolynomial, energyPolynomial,
    denominatorPolynomial, crossingNumeratorPolynomial, crossingPolynomial,
    crossing8Coefficients, Fin.sum_univ_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial, Nat.factorial]
  ring

theorem crossing8_coefficients_ge_margin (a : BernsteinIndex (fun _ : Fin 1 => 6)) :
    crossing8Margin ≤ crossing8Coefficients (a 0) := by
  generalize a 0 = b
  fin_cases b <;> norm_num [crossing8Coefficients, crossing8Margin]

def crossing8Certificate : BernsteinCertificate crossingPolynomial
    (fun _ => (2 : ℚ) / 5) (fun _ => (9 : ℚ) / 20) where
  degree := fun _ => 6
  coefficients := fun a => crossing8Coefficients (a 0)
  margin := crossing8Margin
  identity := crossing8_coefficient_identity
  coefficient_bound := crossing8_coefficients_ge_margin

theorem crossing8_polynomial_pos (t : ℝ) (ht : ((2 : ℚ) / 5 : ℝ) ≤ t)
    (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) : 0 < rationalEval (fun _ : Fin 1 => t) crossingPolynomial := by
  exact crossing8Certificate.pos (by intro i; norm_num)
    (by norm_num [crossing8Certificate, crossing8Margin]) (fun _ => t)
    (fun _ => by norm_num at *; exact ⟨ht, ht1⟩)

/-- Coverage of all nine closed subintervals. -/
theorem crossing_polynomial_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) crossingPolynomial := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact crossing0_polynomial_pos t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact crossing1_polynomial_pos t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact crossing2_polynomial_pos t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact crossing3_polynomial_pos t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact crossing4_polynomial_pos t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact crossing5_polynomial_pos t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact crossing6_polynomial_pos t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact crossing7_polynomial_pos t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact crossing8_polynomial_pos t (by norm_num at *; linarith) (by norm_num at *; linarith)

theorem denominator_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) : 0 < denominator t := by
  have h := denominator_polynomial_pos t (by simpa using ht) (by simpa using ht1)
  simpa [rationalEval, denominatorPolynomial, dominationPolynomial, energyPolynomial,
    heightPolynomial, denominator, domination, energy, height, inv_mul_eq_div] using h

theorem crossing_guard (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < (13 / 25) * denominator t - crossingNumerator t := by
  have h := crossing_polynomial_pos t ht ht1
  simpa [rationalEval, crossingPolynomial, crossingNumeratorPolynomial, denominatorPolynomial,
    dominationPolynomial, energyPolynomial, heightPolynomial, crossingNumerator,
    denominator, domination, energy, height, inv_mul_eq_div] using h

theorem crossingBound_lt_thirteen_fiftieths (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    crossingBound t < 13 / 50 := by
  have hd := denominator_pos t ht ht1
  have hg := crossing_guard t ht ht1
  rw [crossingBound, div_lt_iff₀ (by positivity : 0 < 2 * denominator t)]
  linarith

theorem domination_ge_eleven_twentieths {t : ℝ} (ht1 : t ≤ 9 / 20) :
    11 / 20 ≤ domination t := by unfold domination; linarith

theorem height_lt_four_thirds {t : ℝ} (ht1 : t ≤ 9 / 20) :
    height t < 4 / 3 := by unfold height; linarith

theorem energy_nonneg {t : ℝ} (ht : 0 ≤ t) (hphys : t ^ 2 ≤ 120 / 601) :
    0 ≤ energy t := by
  apply mul_nonneg (show 0 ≤ height t by unfold height; linarith)
  nlinarith

theorem crossingBound_nonneg {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20)
    (hphys : t ^ 2 ≤ 120 / 601) : 0 ≤ crossingBound t := by
  have hh := energy_nonneg ht hphys
  have hd := denominator_pos t ht ht1
  have hq := domination_ge_eleven_twentieths ht1
  have he : energy t < (19 / 100) * domination t := by unfold denominator at hd; linarith
  exact div_nonneg (mul_nonneg hh (by linarith)) (by positivity)


theorem physical_parameter_sq_le {delta : ℝ} (hd0 : 0 ≤ delta)
    (hdg : delta ≤ dittertConstant 5) : fiveDeficitParameter delta ^ 2 ≤ 120 / 601 := by
  have hg : dittertConstant 5 = 24 / 625 := by norm_num [dittertConstant, Nat.factorial]
  have hd1 : delta < 1 := by rw [hg] at hdg; linarith
  rw [fiveDeficitParameter_sq hd0 hd1, div_le_iff₀ (by linarith : 0 < 1 - delta)]
  rw [hg] at hdg
  linarith

theorem energy_of_deficit {delta : ℝ} (hd0 : 0 ≤ delta) (hd1 : delta < 1) :
    energy (fiveDeficitParameter delta) =
      height (fiveDeficitParameter delta) * (dittertConstant 5 - delta) / (1 - delta) := by
  have hg : dittertConstant 5 = 24 / 625 := by norm_num [dittertConstant, Nat.factorial]
  rw [energy, fiveDeficitParameter_sq hd0 hd1, hg]
  field_simp [show 1 - delta ≠ 0 by linarith]
  ring

theorem fiveDeficitParameter_inverse {delta : ℝ} (hd0 : 0 ≤ delta) (hd1 : delta < 1) :
    fiveDeficitParameter delta ^ 2 / (5 + fiveDeficitParameter delta ^ 2) = delta := by
  rw [fiveDeficitParameter_sq hd0 hd1]
  have hp : 0 < 5 + 5 * delta / (1 - delta) := by positivity
  apply (div_eq_iff hp.ne').mpr
  field_simp [show 1 - delta ≠ 0 by linarith]
  ring

theorem physical_crossingBound_nonneg {delta : ℝ} (hd0 : 0 ≤ delta)
    (hdg : delta ≤ dittertConstant 5) : 0 ≤ crossingBound (fiveDeficitParameter delta) :=
  crossingBound_nonneg (fiveDeficitParameter_nonneg _) (fiveDeficitParameter_lt_cap hd0 hdg).le
    (physical_parameter_sq_le hd0 hdg)

end
end DittertRybin.Certificates.SpectralFiveGuards
