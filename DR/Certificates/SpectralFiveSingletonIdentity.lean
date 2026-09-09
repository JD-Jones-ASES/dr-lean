import DR.Certificates.SpectralFiveSingletonCoefficientCheck
import DR.Certificates.SpectralFiveSingletonPowerIdentity
import DR.Certificates.BernsteinTensorRational

/-! The exact staged x/y Bernstein identity for the literal singleton numerator. -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators
open MvPolynomial
set_option maxHeartbeats 4000000

def singletonBlockPolynomial (i : Fin 8) (j : Fin 7) : MvPolynomial (Fin 3) ℚ :=
  ∑ k : Fin 37, C (blockPowerCoefficients i j k) * X 0 ^ (k : ℕ)

private theorem singleton_transformed_coefficient (i : Fin 8) (j : Fin 7) :
    algebraBernsteinCoefficient (fun b : Fin 7 => algebraBernsteinCoefficient
      (fun a : Fin 8 => ∑ k : Fin 37, C (singletonPowerCoefficients a b k) *
        X (0 : Fin 3) ^ (k : ℕ)) i) j = singletonBlockPolynomial i j := by
  simp only [← MvPolynomial.algebraMap_eq]
  rw [double_bernstein_coefficient_power_sum]
  unfold singletonBlockPolynomial
  apply Finset.sum_congr rfl
  intro k hk
  rw [← singletonCoefficientMatch_all i j k]
  rfl

/-- The actual scaled numerator equals the complete 8-by-7 Bernstein blend. -/
theorem scaledSingletonPolynomial_eq_bernstein : scaledSingletonPolynomial =
    ∑ i : Fin 8, ∑ j : Fin 7,
      singletonBlockPolynomial i j *
        (C ((7 : ℕ).choose i : ℚ) * X (1 : Fin 3) ^ (i : ℕ) * ((1 : MvPolynomial (Fin 3) ℚ) - X (1 : Fin 3)) ^ (7 - (i : ℕ))) *
        (C ((6 : ℕ).choose j : ℚ) * X (2 : Fin 3) ^ (j : ℕ) * ((1 : MvPolynomial (Fin 3) ℚ) - X (2 : Fin 3)) ^ (6 - (j : ℕ))) := by
  rw [scaledSingletonPolynomial_eq_power]
  have h := double_power_bernstein_expansion
    (fun a : Fin 8 => fun b : Fin 7 => ∑ k : Fin 37,
      C (singletonPowerCoefficients a b k) * X (0 : Fin 3) ^ (k : ℕ)) (X (1 : Fin 3)) (X (2 : Fin 3))
  simp_rw [singleton_transformed_coefficient] at h
  simpa only [singletonPowerPolynomial, Finset.sum_mul, algebraBernsteinBasis,
    map_natCast, mul_assoc] using h

end
end DittertRybin.Certificates.SpectralFiveSingleton
