import DR.Certificates.BernsteinTransform

/-! Successive exact Bernstein conversion in two axes with arbitrary rational-algebra coefficients. -/

namespace DittertRybin.Certificates
noncomputable section
open scoped BigOperators

def algebraBernsteinCoefficient {R : Type*} [CommRing R] [Algebra ℚ R]
    {n : ℕ} (p : Fin (n + 1) → R) (i : Fin (n + 1)) : R :=
  ∑ k, p k * algebraMap ℚ R (((i : ℕ).choose k : ℚ) / (n.choose k : ℚ))

def algebraBernsteinBasis {R : Type*} [CommRing R]
    (n : ℕ) (i : Fin (n + 1)) (x : R) : R :=
  (n.choose i : R) * x ^ (i : ℕ) * (1 - x) ^ (n - i)

theorem algebraBernstein_expansion {R : Type*} [CommRing R] [Algebra ℚ R]
    {n : ℕ} (p : Fin (n + 1) → R) (x : R) :
    (∑ k, p k * x ^ (k : ℕ)) = ∑ i, algebraBernsteinCoefficient p i * algebraBernsteinBasis n i x :=
  power_sum_bernstein_expansion p x

theorem algebraBernsteinCoefficient_sum {R : Type*} [CommRing R] [Algebra ℚ R]
    {n : ℕ} {ι : Type*} [Fintype ι] (p : ι → Fin (n + 1) → R) (i : Fin (n + 1)) :
    algebraBernsteinCoefficient (fun k => ∑ j, p j k) i = ∑ j, algebraBernsteinCoefficient (p j) i := by
  simp only [algebraBernsteinCoefficient, Finset.sum_mul]
  exact Finset.sum_comm

theorem algebraBernsteinCoefficient_mul {R : Type*} [CommRing R] [Algebra ℚ R]
    {n : ℕ} (p : Fin (n + 1) → R) (c : R) (i : Fin (n + 1)) :
    algebraBernsteinCoefficient (fun k => p k * c) i = algebraBernsteinCoefficient p i * c := by
  simp only [algebraBernsteinCoefficient, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Convert the x and y axes successively; coefficients may themselves be polynomials in other axes. -/
theorem double_power_bernstein_expansion {R : Type*} [CommRing R] [Algebra ℚ R]
    {n m : ℕ} (p : Fin (n + 1) → Fin (m + 1) → R) (x y : R) :
    (∑ a, ∑ b, p a b * x ^ (a : ℕ) * y ^ (b : ℕ)) =
      ∑ i : Fin (n + 1), ∑ j : Fin (m + 1),
        algebraBernsteinCoefficient (fun b => algebraBernsteinCoefficient (fun a => p a b) i) j *
          algebraBernsteinBasis n i x * algebraBernsteinBasis m j y := by
  calc
    _ = ∑ a, (∑ b, p a b * y ^ (b : ℕ)) * x ^ (a : ℕ) := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = ∑ i, algebraBernsteinCoefficient (fun a => ∑ b, p a b * y ^ (b : ℕ)) i *
        algebraBernsteinBasis n i x := algebraBernstein_expansion _ x
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [algebraBernsteinCoefficient_sum]
      simp_rw [algebraBernsteinCoefficient_mul]
      rw [algebraBernstein_expansion, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring

end
end DittertRybin.Certificates
