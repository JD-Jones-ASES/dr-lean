import DR.Certificates.Bernstein
import DR.Square.SixMarginalBounds
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.CharZero.Infinite

/-!
# Exact scalar guards for the order-six spectral argument

The rational polynomials control denominator signs and crossing bounds
for the order-six scalar comparison. Every complete coefficient table has
a proved rational polynomial identity and a positive checked margin on the
entire closed interval [0,31/100]. No sampled numerical signs are used.
-/

namespace DittertRybin.Certificates.SpectralSixGuards
open scoped BigOperators
noncomputable section
open MvPolynomial

def heightPolynomial : MvPolynomial (Fin 1) ℚ := 1 + C (71 / 100) * X 0
def dominationPolynomial : MvPolynomial (Fin 1) ℚ :=
  1 - C (243 / 250) * X 0 - C (41 / 1000) * X 0 ^ 2
def energyPolynomial : MvPolynomial (Fin 1) ℚ :=
  heightPolynomial * (C (5 / 324) - C ((1 - 5 / 324) / 6) * X 0 ^ 2)
def denominatorPolynomial : MvPolynomial (Fin 1) ℚ :=
  C (2 / 15) * dominationPolynomial - energyPolynomial
def crossingNumeratorPolynomial : MvPolynomial (Fin 1) ℚ :=
  energyPolynomial * (2 * dominationPolynomial - energyPolynomial)
def permanentBasePolynomial : MvPolynomial (Fin 1) ℚ :=
  4 * dominationPolynomial * denominatorPolynomial - crossingNumeratorPolynomial
def cellCorrection : ℚ := (5 / 324) ^ 2 / (2 * (2 - 5 / 324) ^ 3)
def cellFloorPolynomial : MvPolynomial (Fin 1) ℚ :=
  C (4 * (1 - cellCorrection)) * denominatorPolynomial - crossingNumeratorPolynomial
def smallBlockPolynomial : MvPolynomial (Fin 1) ℚ :=
  C (2 / 5) * dominationPolynomial * denominatorPolynomial - crossingNumeratorPolynomial
def crossingPolynomial : MvPolynomial (Fin 1) ℚ :=
  C (1 / 3) * denominatorPolynomial - crossingNumeratorPolynomial

def height (t : ℝ) : ℝ := 1 + (71 / 100) * t
def energy (t : ℝ) : ℝ := height t * ((5 / 324) - ((1 - 5 / 324) / 6) * t ^ 2)
def denominator (t : ℝ) : ℝ := (2 / 15) * sixDominationFactor t - energy t
def crossingNumerator (t : ℝ) : ℝ := energy t * (2 * sixDominationFactor t - energy t)
def crossingBound (t : ℝ) : ℝ := crossingNumerator t / (2 * denominator t)

def denominatorCoefficients : Fin 4 → ℚ := ![(191 : ℚ) / 1620,
  (25120619 : ℚ) / 243000000,
  (3423902113 : ℚ) / 36450000000,
  (6029228189 : ℚ) / 64800000000]
def denominatorMargin : ℚ := (6029228189 : ℚ) / 64800000000

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem denominator_coefficient_identity :
    affineNormalize (fun _ : Fin 1 ↦ (0 : ℚ)) (fun _ ↦ (31 : ℚ) / 100) denominatorPolynomial =
      tensorPolynomial (fun _ : Fin 1 ↦ 3) (fun a ↦ denominatorCoefficients (a 0)) := by
  apply MvPolynomial.funext
  intro x
  rw [tensorPolynomial_one]
  norm_num [affineNormalize, denominatorPolynomial, heightPolynomial, dominationPolynomial, energyPolynomial, denominatorPolynomial, crossingNumeratorPolynomial, permanentBasePolynomial, cellFloorPolynomial, smallBlockPolynomial, crossingPolynomial, cellCorrection, denominatorCoefficients, Fin.sum_univ_succ, Nat.choose]
  ring

theorem denominator_coefficients_ge_margin (a : BernsteinIndex (fun _ : Fin 1 ↦ 3)) :
    denominatorMargin ≤ denominatorCoefficients (a 0) := by
  generalize a 0 = b
  fin_cases b <;> norm_num [denominatorCoefficients, denominatorMargin]

def denominatorCertificate : BernsteinCertificate denominatorPolynomial
    (fun _ ↦ (0 : ℚ)) (fun _ ↦ (31 : ℚ) / 100) where
  degree := fun _ ↦ 3
  coefficients := fun a ↦ denominatorCoefficients (a 0)
  margin := denominatorMargin
  identity := denominator_coefficient_identity
  coefficient_bound := denominator_coefficients_ge_margin

theorem denominator_polynomial_pos (t : ℝ) (ht : ((0 : ℚ) : ℝ) ≤ t) (ht1 : t ≤ ((31 : ℚ) / 100 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 ↦ t) denominatorPolynomial := by
  exact denominatorCertificate.pos (by intro i; norm_num)
    (by norm_num [denominatorCertificate, denominatorMargin])
    (fun _ ↦ t) (fun _ ↦ by norm_num at *; exact ⟨ht, ht1⟩)

def smallBlockCoefficients : Fin 7 → ℚ := ![(43393 : ℚ) / 2624400,
  (4604434837 : ℚ) / 393660000000,
  (2898784559044699 : ℚ) / 295245000000000000,
  (13216211075254027 : ℚ) / 1230187500000000000,
  (125356630874343205603 : ℚ) / 8857350000000000000000,
  (9248902807952477641 : ℚ) / 472392000000000000000,
  (110974804266181421641 : ℚ) / 4199040000000000000000]
def smallBlockMargin : ℚ := (2898784559044699 : ℚ) / 295245000000000000

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem smallBlock_coefficient_identity :
    affineNormalize (fun _ : Fin 1 ↦ (0 : ℚ)) (fun _ ↦ (31 : ℚ) / 100) smallBlockPolynomial =
      tensorPolynomial (fun _ : Fin 1 ↦ 6) (fun a ↦ smallBlockCoefficients (a 0)) := by
  apply MvPolynomial.funext
  intro x
  rw [tensorPolynomial_one]
  norm_num [affineNormalize, smallBlockPolynomial, heightPolynomial, dominationPolynomial, energyPolynomial, denominatorPolynomial, crossingNumeratorPolynomial, permanentBasePolynomial, cellFloorPolynomial, smallBlockPolynomial, crossingPolynomial, cellCorrection, smallBlockCoefficients, Fin.sum_univ_succ, Nat.choose]
  ring

theorem smallBlock_coefficients_ge_margin (a : BernsteinIndex (fun _ : Fin 1 ↦ 6)) :
    smallBlockMargin ≤ smallBlockCoefficients (a 0) := by
  generalize a 0 = b
  fin_cases b <;> norm_num [smallBlockCoefficients, smallBlockMargin]

def smallBlockCertificate : BernsteinCertificate smallBlockPolynomial
    (fun _ ↦ (0 : ℚ)) (fun _ ↦ (31 : ℚ) / 100) where
  degree := fun _ ↦ 6
  coefficients := fun a ↦ smallBlockCoefficients (a 0)
  margin := smallBlockMargin
  identity := smallBlock_coefficient_identity
  coefficient_bound := smallBlock_coefficients_ge_margin

theorem smallBlock_polynomial_pos (t : ℝ) (ht : ((0 : ℚ) : ℝ) ≤ t) (ht1 : t ≤ ((31 : ℚ) / 100 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 ↦ t) smallBlockPolynomial := by
  exact smallBlockCertificate.pos (by intro i; norm_num)
    (by norm_num [smallBlockCertificate, smallBlockMargin])
    (fun _ ↦ t) (fun _ ↦ by norm_num at *; exact ⟨ht, ht1⟩)

def crossingCoefficients : Fin 7 → ℚ := ![(4553 : ℚ) / 524880,
  (526633151 : ℚ) / 78732000000,
  (3428504667211 : ℚ) / 472392000000000,
  (162207062984663 : ℚ) / 15746400000000000,
  (1105892656850134607 : ℚ) / 70858800000000000000,
  (2697796751106026899 : ℚ) / 118098000000000000000,
  (132633852663030596329 : ℚ) / 4199040000000000000000]
def crossingMargin : ℚ := (526633151 : ℚ) / 78732000000

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem crossing_coefficient_identity :
    affineNormalize (fun _ : Fin 1 ↦ (0 : ℚ)) (fun _ ↦ (31 : ℚ) / 100) crossingPolynomial =
      tensorPolynomial (fun _ : Fin 1 ↦ 6) (fun a ↦ crossingCoefficients (a 0)) := by
  apply MvPolynomial.funext
  intro x
  rw [tensorPolynomial_one]
  norm_num [affineNormalize, crossingPolynomial, heightPolynomial, dominationPolynomial, energyPolynomial, denominatorPolynomial, crossingNumeratorPolynomial, permanentBasePolynomial, cellFloorPolynomial, smallBlockPolynomial, crossingPolynomial, cellCorrection, crossingCoefficients, Fin.sum_univ_succ, Nat.choose]
  ring

theorem crossing_coefficients_ge_margin (a : BernsteinIndex (fun _ : Fin 1 ↦ 6)) :
    crossingMargin ≤ crossingCoefficients (a 0) := by
  generalize a 0 = b
  fin_cases b <;> norm_num [crossingCoefficients, crossingMargin]

def crossingCertificate : BernsteinCertificate crossingPolynomial
    (fun _ ↦ (0 : ℚ)) (fun _ ↦ (31 : ℚ) / 100) where
  degree := fun _ ↦ 6
  coefficients := fun a ↦ crossingCoefficients (a 0)
  margin := crossingMargin
  identity := crossing_coefficient_identity
  coefficient_bound := crossing_coefficients_ge_margin

theorem crossing_polynomial_pos (t : ℝ) (ht : ((0 : ℚ) : ℝ) ≤ t) (ht1 : t ≤ ((31 : ℚ) / 100 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 ↦ t) crossingPolynomial := by
  exact crossingCertificate.pos (by intro i; norm_num)
    (by norm_num [crossingCertificate, crossingMargin])
    (fun _ ↦ t) (fun _ ↦ by norm_num at *; exact ⟨ht, ht1⟩)

def permanentBaseCoefficients : Fin 7 → ℚ := ![(231461 : ℚ) / 524880,
  (30601692149 : ℚ) / 78732000000,
  (20433462971913023 : ℚ) / 59049000000000000,
  (615553285085149807 : ℚ) / 1968300000000000000,
  (510182373678718624631 : ℚ) / 1771470000000000000000,
  (63929306181571404023 : ℚ) / 236196000000000000000,
  (1088125328636138849449 : ℚ) / 4199040000000000000000]
def permanentBaseMargin : ℚ := (1088125328636138849449 : ℚ) / 4199040000000000000000

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem permanentBase_coefficient_identity :
    affineNormalize (fun _ : Fin 1 ↦ (0 : ℚ)) (fun _ ↦ (31 : ℚ) / 100) permanentBasePolynomial =
      tensorPolynomial (fun _ : Fin 1 ↦ 6) (fun a ↦ permanentBaseCoefficients (a 0)) := by
  apply MvPolynomial.funext
  intro x
  rw [tensorPolynomial_one]
  norm_num [affineNormalize, permanentBasePolynomial, heightPolynomial, dominationPolynomial, energyPolynomial, denominatorPolynomial, crossingNumeratorPolynomial, permanentBasePolynomial, cellFloorPolynomial, smallBlockPolynomial, crossingPolynomial, cellCorrection, permanentBaseCoefficients, Fin.sum_univ_succ, Nat.choose]
  ring

theorem permanentBase_coefficients_ge_margin (a : BernsteinIndex (fun _ : Fin 1 ↦ 6)) :
    permanentBaseMargin ≤ permanentBaseCoefficients (a 0) := by
  generalize a 0 = b
  fin_cases b <;> norm_num [permanentBaseCoefficients, permanentBaseMargin]

def permanentBaseCertificate : BernsteinCertificate permanentBasePolynomial
    (fun _ ↦ (0 : ℚ)) (fun _ ↦ (31 : ℚ) / 100) where
  degree := fun _ ↦ 6
  coefficients := fun a ↦ permanentBaseCoefficients (a 0)
  margin := permanentBaseMargin
  identity := permanentBase_coefficient_identity
  coefficient_bound := permanentBase_coefficients_ge_margin

theorem permanentBase_polynomial_pos (t : ℝ) (ht : ((0 : ℚ) : ℝ) ≤ t) (ht1 : t ≤ ((31 : ℚ) / 100 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 ↦ t) permanentBasePolynomial := by
  exact permanentBaseCertificate.pos (by intro i; norm_num)
    (by norm_num [permanentBaseCertificate, permanentBaseMargin])
    (fun _ ↦ t) (fun _ ↦ by norm_num at *; exact ⟨ht, ht1⟩)

def cellFloorCoefficients : Fin 7 → ℚ := ![(61532373589127 : ℚ) / 139538144450160,
  (8630971784492687159 : ℚ) / 20930721667524000000,
  (48981261937130524498441 : ℚ) / 125584330005144000000000,
  (1567844792969746216227191 : ℚ) / 4186144333504800000000000,
  (6900198323021562585344796149 : ℚ) / 18837649500771600000000000000,
  (11479373425185879306868220593 : ℚ) / 31396082501286000000000000000,
  (416092778150896882289707267603 : ℚ) / 1116305155601280000000000000000]
def cellFloorMargin : ℚ := (11479373425185879306868220593 : ℚ) / 31396082501286000000000000000

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem cellFloor_coefficient_identity :
    affineNormalize (fun _ : Fin 1 ↦ (0 : ℚ)) (fun _ ↦ (31 : ℚ) / 100) cellFloorPolynomial =
      tensorPolynomial (fun _ : Fin 1 ↦ 6) (fun a ↦ cellFloorCoefficients (a 0)) := by
  apply MvPolynomial.funext
  intro x
  rw [tensorPolynomial_one]
  norm_num [affineNormalize, cellFloorPolynomial, heightPolynomial, dominationPolynomial, energyPolynomial, denominatorPolynomial, crossingNumeratorPolynomial, permanentBasePolynomial, cellFloorPolynomial, smallBlockPolynomial, crossingPolynomial, cellCorrection, cellFloorCoefficients, Fin.sum_univ_succ, Nat.choose]
  ring

theorem cellFloor_coefficients_ge_margin (a : BernsteinIndex (fun _ : Fin 1 ↦ 6)) :
    cellFloorMargin ≤ cellFloorCoefficients (a 0) := by
  generalize a 0 = b
  fin_cases b <;> norm_num [cellFloorCoefficients, cellFloorMargin]

def cellFloorCertificate : BernsteinCertificate cellFloorPolynomial
    (fun _ ↦ (0 : ℚ)) (fun _ ↦ (31 : ℚ) / 100) where
  degree := fun _ ↦ 6
  coefficients := fun a ↦ cellFloorCoefficients (a 0)
  margin := cellFloorMargin
  identity := cellFloor_coefficient_identity
  coefficient_bound := cellFloor_coefficients_ge_margin

theorem cellFloor_polynomial_pos (t : ℝ) (ht : ((0 : ℚ) : ℝ) ≤ t) (ht1 : t ≤ ((31 : ℚ) / 100 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 ↦ t) cellFloorPolynomial := by
  exact cellFloorCertificate.pos (by intro i; norm_num)
    (by norm_num [cellFloorCertificate, cellFloorMargin])
    (fun _ ↦ t) (fun _ ↦ by norm_num at *; exact ⟨ht, ht1⟩)


/-- The alternating inversion denominator is positive on the entire certificate interval. -/
theorem denominator_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 31 / 100) : 0 < denominator t := by
  have h := denominator_polynomial_pos t (by simpa using ht) (by simpa using ht1)
  simpa [rationalEval, denominatorPolynomial, energyPolynomial, dominationPolynomial,
    heightPolynomial, denominator, energy, height, sixDominationFactor] using h

theorem small_block_guard (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 31 / 100) :
    0 < (2 / 5 : ℝ) * sixDominationFactor t * denominator t - crossingNumerator t := by
  have h := smallBlock_polynomial_pos t (by simpa using ht) (by simpa using ht1)
  simpa [rationalEval, smallBlockPolynomial, denominatorPolynomial, energyPolynomial,
    crossingNumeratorPolynomial, dominationPolynomial, heightPolynomial,
    denominator, energy, height, crossingNumerator, sixDominationFactor] using h

set_option maxHeartbeats 2000000 in
theorem crossing_guard (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 31 / 100) :
    0 < denominator t / 3 - crossingNumerator t := by
  have h := crossing_polynomial_pos t (by simpa using ht) (by simpa using ht1)
  simpa [rationalEval, crossingPolynomial, denominatorPolynomial, energyPolynomial,
    crossingNumeratorPolynomial, dominationPolynomial, heightPolynomial,
    denominator, energy, height, crossingNumerator, sixDominationFactor, div_eq_mul_inv,
    mul_comm] using h

theorem permanent_base_guard (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 31 / 100) :
    0 < 4 * sixDominationFactor t * denominator t - crossingNumerator t := by
  have h := permanentBase_polynomial_pos t (by simpa using ht) (by simpa using ht1)
  simpa [rationalEval, permanentBasePolynomial, denominatorPolynomial, energyPolynomial,
    crossingNumeratorPolynomial, dominationPolynomial, heightPolynomial,
    denominator, energy, height, crossingNumerator, sixDominationFactor] using h

theorem cell_floor_guard (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 31 / 100) :
    0 < 4 * (1 - (cellCorrection : ℝ)) * denominator t - crossingNumerator t := by
  have h := cellFloor_polynomial_pos t (by simpa using ht) (by simpa using ht1)
  simpa [rationalEval, cellFloorPolynomial, denominatorPolynomial, energyPolynomial,
    crossingNumeratorPolynomial, dominationPolynomial, heightPolynomial,
    denominator, energy, height, crossingNumerator, sixDominationFactor] using h

/-- The numerator certificate proves the strict bound without assuming its sign. -/
theorem crossingBound_lt_one_sixth (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 31 / 100) :
    crossingBound t < 1 / 6 := by
  have hd := denominator_pos t ht ht1
  have hg := crossing_guard t ht ht1
  rw [crossingBound, div_lt_iff₀ (by positivity : 0 < 2 * denominator t)]
  linarith

theorem normalized_crossing_lt_one_tenth (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 31 / 100) :
    crossingBound t / (2 * sixDominationFactor t) < 1 / 10 := by
  have hd := denominator_pos t ht ht1
  have hq := sixDominationFactor_gt_two_thirds ht ht1
  have hg := small_block_guard t ht ht1
  rw [div_lt_iff₀ (by linarith : 0 < 2 * sixDominationFactor t), crossingBound,
    div_lt_iff₀ (by positivity : 0 < 2 * denominator t)]
  nlinarith

theorem permanent_base_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 31 / 100) :
    0 < sixDominationFactor t - crossingBound t / 2 := by
  have hd := denominator_pos t ht ht1
  have hg := permanent_base_guard t ht ht1
  have heq : sixDominationFactor t - crossingBound t / 2 =
      (4 * sixDominationFactor t * denominator t - crossingNumerator t) / (4 * denominator t) := by
    unfold crossingBound
    field_simp
    ring
  rw [heq]
  exact div_pos hg (by positivity)

theorem cell_floor_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 31 / 100) :
    0 < 1 - crossingBound t / 2 - (cellCorrection : ℝ) := by
  have hd := denominator_pos t ht ht1
  have hg := cell_floor_guard t ht ht1
  have heq : 1 - crossingBound t / 2 - (cellCorrection : ℝ) =
      (4 * (1 - (cellCorrection : ℝ)) * denominator t - crossingNumerator t) /
        (4 * denominator t) := by
    unfold crossingBound
    field_simp
    ring
  rw [heq]
  exact div_pos hg (by positivity)

/-- Nonnegativity of the energy uses the physical interval, rather than the
slightly longer interval used for the polynomial positivity guards. -/
theorem energy_nonneg {t : ℝ} (ht : 0 ≤ t) (hphysical : t ^ 2 ≤ 30 / 319) :
    0 ≤ energy t := by
  apply mul_nonneg (show 0 ≤ height t by unfold height; linarith)
  nlinarith

theorem crossingBound_nonneg {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 31 / 100)
    (hphysical : t ^ 2 ≤ 30 / 319) : 0 ≤ crossingBound t := by
  have hd := denominator_pos t ht ht1
  have hq := sixDominationFactor_gt_two_thirds ht ht1
  have he := energy_nonneg ht hphysical
  have hbr : 0 ≤ 2 * sixDominationFactor t - energy t := by
    unfold denominator at hd
    linarith
  exact div_nonneg (mul_nonneg he hbr) (by positivity)

theorem height_lt_five_fourths {t : ℝ} (ht1 : t ≤ 31 / 100) : height t < 5 / 4 := by
  unfold height
  linarith

theorem ordinary_path_gap_guard : (2 / 3 : ℝ) * (1 / 15) > (5 / 4) * dittertConstant 6 := by
  norm_num [dittertConstant, Nat.factorial]

theorem cosine_rational_guard : (3 / 4 : ℝ) < (13 / 15) ^ 2 := by norm_num


/-- The true deficit interval lies inside the certified physical energy interval. -/
theorem physical_parameter_sq_le {delta : ℝ} (hd0 : 0 ≤ delta)
    (hdg : delta ≤ dittertConstant 6) : sixDeficitParameter delta ^ 2 ≤ 30 / 319 := by
  have hg : dittertConstant 6 = 5 / 324 := by norm_num [dittertConstant, Nat.factorial]
  have hden : 0 < 1 - delta := by rw [hg] at hdg; linarith
  rw [sixDeficitParameter_sq hd0 (by linarith), div_le_iff₀ hden]
  rw [hg] at hdg
  linarith

/-- Substitution of the actual parameter gives the energy envelope in the
original permanent-deficit variables, with its denominator explicit. -/
theorem energy_of_deficit {delta : ℝ} (hd0 : 0 ≤ delta) (hd1 : delta < 1) :
    energy (sixDeficitParameter delta) =
      height (sixDeficitParameter delta) * (dittertConstant 6 - delta) / (1 - delta) := by
  have hden : 1 - delta ≠ 0 := by linarith
  rw [energy, sixDeficitParameter_sq hd0 hd1]
  norm_num [dittertConstant, Nat.factorial]
  field_simp
  ring

theorem physical_crossingBound_nonneg {delta : ℝ} (hd0 : 0 ≤ delta)
    (hdg : delta ≤ dittertConstant 6) : 0 ≤ crossingBound (sixDeficitParameter delta) :=
  crossingBound_nonneg (sixDeficitParameter_nonneg delta)
    (sixDeficitParameter_le_cap hd0 hdg).le (physical_parameter_sq_le hd0 hdg)

end
end DittertRybin.Certificates.SpectralSixGuards
