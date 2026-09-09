import DR.Certificates.SpectralFiveSingletonSparseCheck

/-! Exact literal-numerator identity through independently checked sparse arithmetic. -/
namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators
open MvPolynomial

def singletonPowerPolynomial : MvPolynomial (Fin 3) ℚ :=
  ∑ i : Fin 8, ∑ j : Fin 7, ∑ k : Fin 37,
    C (singletonPowerCoefficients i j k) * X 0 ^ (k : ℕ) * X 1 ^ (i : ℕ) * X 2 ^ (j : ℕ)

/-- The sparse power table is the actual factored numerator, with no coefficient assumptions. -/
theorem scaledSingletonPolynomial_eq_power : scaledSingletonPolynomial = singletonPowerPolynomial := by
  rw [← singletonSparseSource_value, singletonSparseCheck]
  simp only [SparsePolynomial.value_fromTensor, MvPolynomial.algebraMap_eq,
    singletonPowerPolynomial]

end
end DittertRybin.Certificates.SpectralFiveSingleton
