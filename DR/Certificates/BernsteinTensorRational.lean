import DR.Certificates.BernsteinTensorTransform

/-! Rational coefficient conversion commutes with a remaining polynomial axis. -/
namespace DittertRybin.Certificates
noncomputable section
open scoped BigOperators

theorem algebraBernsteinCoefficient_map_rat {R : Type*} [CommRing R] [Algebra ℚ R]
    {n : ℕ} (p : Fin (n + 1) → ℚ) (i : Fin (n + 1)) :
    algebraBernsteinCoefficient (fun k => algebraMap ℚ R (p k)) i =
      algebraMap ℚ R (powerToBernstein p i) := by
  simp only [algebraBernsteinCoefficient, powerToBernstein, map_sum,
    div_eq_mul_inv, map_mul, mul_assoc]

theorem double_bernstein_coefficient_power_sum {R : Type*} [CommRing R] [Algebra ℚ R]
    {n m l : ℕ} (p : Fin (n + 1) → Fin (m + 1) → Fin (l + 1) → ℚ)
    (t : R) (i : Fin (n + 1)) (j : Fin (m + 1)) :
    algebraBernsteinCoefficient (fun b => algebraBernsteinCoefficient
      (fun a => ∑ k, algebraMap ℚ R (p a b k) * t ^ (k : ℕ)) i) j =
      ∑ k, algebraMap ℚ R (powerToBernstein
        (fun b => powerToBernstein (fun a => p a b k) i) j) * t ^ (k : ℕ) := by
  simp_rw [algebraBernsteinCoefficient_sum, algebraBernsteinCoefficient_mul]
  simp_rw [algebraBernsteinCoefficient_map_rat]

end
end DittertRybin.Certificates
