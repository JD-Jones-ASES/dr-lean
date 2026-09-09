import DR.Certificates.Bernstein

/-!
# Exact conversion from power coefficients to Bernstein coefficients

The conversion is proved once from the binomial theorem. Applications need
only finite rational coefficient checks, rather than expanding a fresh
high-degree Bernstein identity for each interval.
-/

namespace DittertRybin.Certificates

noncomputable section
open scoped BigOperators

/-- The binomial moment identity, before division by its nonzero coefficient. -/
theorem bernstein_binomial_moment {R : Type*} [CommRing R]
    (x : R) (n k : ℕ) (hk : k ≤ n) :
    (∑ j ∈ Finset.range (n + 1),
      (j.choose k : R) * ((n.choose j : R) * x ^ j * (1 - x) ^ (n - j))) =
        (n.choose k : R) * x ^ k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [show k + d + 1 = k + (d + 1) by omega, Finset.sum_range_add]
  have hzero : (∑ j ∈ Finset.range k,
      (j.choose k : R) * (((k + d).choose j : R) * x ^ j * (1 - x) ^ (k + d - j))) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hj)]
  rw [hzero, zero_add]
  calc
    _ = ((k + d).choose k : R) * x ^ k *
        (∑ j ∈ Finset.range (d + 1), x ^ j * (1 - x) ^ (d - j) * (d.choose j : R)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hchoose : ((k + d).choose (k + j) : R) * ((k + j).choose k : R) =
          ((k + d).choose k : R) * (d.choose j : R) := by
        have hc := congrArg (fun a : ℕ => (a : R))
          (Nat.choose_mul (n := k + d) (k := k + j) (s := k) (by omega))
        simpa only [Nat.add_sub_cancel_left, Nat.cast_mul] using hc
      rw [pow_add]
      have hexp : k + d - (k + j) = d - j := by omega
      rw [hexp]
      calc
        _ = (((k + d).choose (k + j) : R) * ((k + j).choose k : R)) *
            x ^ k * x ^ j * (1 - x) ^ (d - j) := by ring
        _ = _ := by rw [hchoose]; ring
    _ = _ := by rw [← add_pow]; simp

/-- Each monomial has its exact degree-n Bernstein representation in every rational algebra. -/
theorem power_bernstein_expansion {R : Type*} [CommRing R] [Algebra ℚ R]
    (x : R) (n k : ℕ) (hk : k ≤ n) :
    x ^ k = ∑ j ∈ Finset.range (n + 1),
      algebraMap ℚ R ((j.choose k : ℚ) / (n.choose k : ℚ)) *
        ((n.choose j : R) * x ^ j * (1 - x) ^ (n - j)) := by
  have hn : (n.choose k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hk).ne'
  calc
    _ = algebraMap ℚ R ((n.choose k : ℚ)⁻¹) *
        ((n.choose k : R) * x ^ k) := by
      rw [← mul_assoc, ← map_natCast (algebraMap ℚ R), ← map_mul,
        inv_mul_cancel₀ hn, map_one, one_mul]
    _ = _ := by
      rw [← bernstein_binomial_moment x n k hk, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [div_eq_mul_inv, map_mul, map_natCast]
      ring

/-- A full finite table of ordinary power coefficients. -/
def powerPolynomial {n : ℕ} (p : Fin (n + 1) → ℚ) : MvPolynomial (Fin 1) ℚ :=
  ∑ k, MvPolynomial.C (p k) * MvPolynomial.X 0 ^ (k : ℕ)

/-- The standard triangular power-to-Bernstein transform, with binomial normalization. -/
def powerToBernstein {n : ℕ} (p : Fin (n + 1) → ℚ) (i : Fin (n + 1)) : ℚ :=
  ∑ k, p k * ((i : ℕ).choose k : ℚ) / (n.choose k : ℚ)

/-- The conversion also permits polynomial-valued coefficients, for successive tensor axes. -/
theorem power_sum_bernstein_expansion {R : Type*} [CommRing R] [Algebra ℚ R]
    {n : ℕ} (p : Fin (n + 1) → R) (x : R) :
    (∑ k, p k * x ^ (k : ℕ)) =
      ∑ j : Fin (n + 1),
        (∑ k : Fin (n + 1), p k * algebraMap ℚ R
          (((j : ℕ).choose k : ℚ) / (n.choose k : ℚ))) *
          ((n.choose j : R) * x ^ (j : ℕ) * (1 - x) ^ (n - j)) := by
  have hpow (k : Fin (n + 1)) : x ^ (k : ℕ) =
      ∑ j : Fin (n + 1), algebraMap ℚ R (((j : ℕ).choose k : ℚ) / (n.choose k : ℚ)) *
        ((n.choose j : R) * x ^ (j : ℕ) * (1 - x) ^ (n - j)) := by
    simpa only [Finset.sum_range] using power_bernstein_expansion x n k (by omega)
  calc
    _ = ∑ k : Fin (n + 1), ∑ j : Fin (n + 1), p k *
        (algebraMap ℚ R (((j : ℕ).choose k : ℚ) / (n.choose k : ℚ)) *
          ((n.choose j : R) * x ^ (j : ℕ) * (1 - x) ^ (n - j))) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hpow k, Finset.mul_sum]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring

/-- Exact identity in the existing one-variable rational tensor certificate format. -/
theorem powerPolynomial_eq_tensorPolynomial {n : ℕ} (p : Fin (n + 1) → ℚ) :
    powerPolynomial p =
      tensorPolynomial (fun _ : Fin 1 => n) (fun a => powerToBernstein p (a 0)) := by
  rw [tensorPolynomial_one]
  have h := power_sum_bernstein_expansion
    (fun k => MvPolynomial.C (p k) : Fin (n + 1) → MvPolynomial (Fin 1) ℚ)
    (MvPolynomial.X 0)
  simpa only [powerPolynomial, powerToBernstein, map_sum, div_eq_mul_inv, map_mul,
    MvPolynomial.algebraMap_eq, map_natCast, mul_assoc] using h

/-- Power coefficients after the exact substitution `lo + (hi-lo) t`. -/
def affinePowerCoefficients {n : ℕ} (lo hi : ℚ) (p : Fin (n + 1) → ℚ)
    (j : Fin (n + 1)) : ℚ :=
  ∑ k, p k * ((k : ℕ).choose j : ℚ) * lo ^ ((k : ℕ) - j) * (hi - lo) ^ (j : ℕ)

/-- A binomial power expanded in a possibly larger finite coefficient table. -/
theorem affine_power_expansion {R : Type*} [CommRing R]
    (a b x : R) (n k : ℕ) (hk : k ≤ n) :
    (a + b * x) ^ k = ∑ j : Fin (n + 1),
      (k.choose j : R) * a ^ (k - j) * b ^ (j : ℕ) * x ^ (j : ℕ) := by
  have hs : (∑ j ∈ Finset.range (n + 1),
      (k.choose j : R) * a ^ (k - j) * b ^ j * x ^ j) =
      ∑ j : Fin (n + 1), (k.choose j : R) * a ^ (k - j) * b ^ (j : ℕ) * x ^ (j : ℕ) := by
    exact Finset.sum_range (fun j => (k.choose j : R) * a ^ (k - j) * b ^ j * x ^ j)
  rw [← hs]
  have he : (∑ j ∈ Finset.range (k + 1),
      (k.choose j : R) * a ^ (k - j) * b ^ j * x ^ j) =
      ∑ j ∈ Finset.range (n + 1),
        (k.choose j : R) * a ^ (k - j) * b ^ j * x ^ j := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j hj hjk
    have hkj : k < j := by simp only [Finset.mem_range] at hjk; omega
    simp [Nat.choose_eq_zero_of_lt hkj]
  rw [← he, add_comm a, add_pow]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_pow]
  ring

/-- Affine substitution is a finite triangular operation over every commutative ring. -/
theorem affine_power_sum_expansion {R : Type*} [CommRing R]
    {n : ℕ} (p : Fin (n + 1) → R) (a b x : R) :
    (∑ k, p k * (a + b * x) ^ (k : ℕ)) =
      ∑ j : Fin (n + 1),
        (∑ k : Fin (n + 1), p k * ((k : ℕ).choose j : R) * a ^ ((k : ℕ) - j) *
          b ^ (j : ℕ)) * x ^ (j : ℕ) := by
  calc
    _ = ∑ k : Fin (n + 1), ∑ j : Fin (n + 1), p k *
        (((k : ℕ).choose j : R) * a ^ ((k : ℕ) - j) * b ^ (j : ℕ) * x ^ (j : ℕ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [affine_power_expansion a b x n k (by omega), Finset.mul_sum]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring

/-- The coefficient transform agrees exactly with the certificate's affine normalization. -/
theorem affineNormalize_powerPolynomial {n : ℕ} (lo hi : ℚ)
    (p : Fin (n + 1) → ℚ) :
    affineNormalize (fun _ => lo) (fun _ => hi) (powerPolynomial p) =
      powerPolynomial (affinePowerCoefficients lo hi p) := by
  have h := affine_power_sum_expansion
    (fun k => MvPolynomial.C (p k) : Fin (n + 1) → MvPolynomial (Fin 1) ℚ)
    (MvPolynomial.C lo) (MvPolynomial.C (hi - lo)) (MvPolynomial.X 0)
  simpa only [affineNormalize, powerPolynomial, affinePowerCoefficients,
    MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow,
    MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, map_sum, map_mul, map_pow, map_natCast] using h

/-- Exact transformed coefficient bounds imply a bound on the whole closed interval. -/
theorem powerPolynomial_box_lower_bound {n : ℕ} (lo hi : ℚ)
    (p : Fin (n + 1) → ℚ) (margin : ℚ) (hwidth : lo < hi)
    (hc : ∀ i, margin ≤ powerToBernstein (affinePowerCoefficients lo hi p) i)
    (x : ℝ) (hx : (lo : ℝ) ≤ x ∧ x ≤ hi) :
    (margin : ℝ) ≤ rationalEval (fun _ : Fin 1 => x) (powerPolynomial p) := by
  apply bernstein_box_lower_bound (powerPolynomial p) (fun _ => lo) (fun _ => hi)
    (fun _ => hwidth) (fun _ => n)
    (fun a => powerToBernstein (affinePowerCoefficients lo hi p) (a 0)) margin
  · rw [affineNormalize_powerPolynomial, powerPolynomial_eq_tensorPolynomial]
  · intro a
    exact hc (a 0)
  · intro i
    exact hx

end
end DittertRybin.Certificates
